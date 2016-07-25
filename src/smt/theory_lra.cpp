/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    theory_lra.cpp

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach) 2016-25-3
    Nikolaj Bjorner (nbjorner)

Revision History:


--*/
#include "util/stopwatch.h"
#include "util/lp/lp_solver.h"
#include "util/lp/lp_primal_simplex.h"
#include "util/lp/lp_dual_simplex.h"
#include "util/lp/indexed_value.h"
#include "util/lp/lar_solver.h"
#include "util/nat_set.h"
#include "util/optional.h"
#include "util/inf_rational.h"
#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "smt/theory_lra.h"
#include "smt/proto_model/numeral_factory.h"
#include "smt/smt_model_generator.h"
#include "smt/arith_eq_adapter.h"

namespace lp {
    enum bound_kind { lower_t, upper_t };

    std::ostream& operator<<(std::ostream& out, bound_kind const& k) {
        switch (k) {
        case lower_t: return out << "<=";
        case upper_t: return out << ">=";
        }
        return out;
    }

    class bound { 
        smt::bool_var     m_bv;
        smt::theory_var  m_var;
        rational         m_value;
        bound_kind       m_bound_kind;

    public:
        bound(smt::bool_var bv, smt::theory_var v, rational const & val, bound_kind k):
            m_bv(bv),
            m_var(v),
            m_value(val),
            m_bound_kind(k) {
        }
        virtual ~bound() {}
        smt::theory_var get_var() const { return m_var; }
        smt::bool_var get_bv() const { return m_bv; }
        bound_kind get_bound_kind() const { return m_bound_kind; }
        rational const& get_value() const { return m_value; }
        inf_rational get_value(bool is_true) const { 
            if (is_true) return inf_rational(m_value);                         // v >= value or v <= value
            if (m_bound_kind == lower_t) return inf_rational(m_value, false);  // v <= value - epsilon
            return inf_rational(m_value, true);                                // v >= value + epsilon
        } 
        virtual std::ostream& display(std::ostream& out) const {
            return out << "v" << get_var() << "  " << get_bound_kind() << " " << m_value;
        }
    };

    std::ostream& operator<<(std::ostream& out, bound const& b) {
        return b.display(out);
    }

    struct stats {
        unsigned m_assert_lower;
        unsigned m_assert_upper;
        unsigned m_add_rows;
        unsigned m_bounds_propagations;
        unsigned m_num_iterations;
        unsigned m_num_iterations_with_no_progress;
        stats() { reset(); }
        void reset() {
            memset(this, 0, sizeof(*this));
        }
    };

    typedef optional<inf_rational> opt_inf_rational;


}

namespace smt {


    class theory_lra::imp {        

        struct scope {
            unsigned m_bounds_lim;
            unsigned m_asserted_qhead;            
            unsigned m_asserted_atoms_lim;
            unsigned m_delayed_terms_lim;
            unsigned m_delayed_equalities_lim;
            unsigned m_delayed_defs_lim;
            unsigned m_underspecified_lim;
            unsigned m_var_trail_lim;
            expr*    m_not_handled;
        };

        struct delayed_atom {
            unsigned m_bv;
            bool     m_is_true;
            delayed_atom(unsigned b, bool t): m_bv(b), m_is_true(t) {}
        };

        class resource_limit : public lean::lp_resource_limit {
            imp& m_imp;
        public:
            resource_limit(imp& i): m_imp(i) { }
            virtual bool get_cancel_flag() { return m_imp.m.canceled(); }
        };


        theory_lra&          th;
        ast_manager&         m;
        theory_arith_params& m_params;
        arith_util           a;

        arith_eq_adapter     m_arith_eq_adapter;

        vector<rational>    m_columns;


        // temporary values kept during internalization
        struct internalize_state {
            expr_ref_vector     m_terms;                     
            vector<rational>    m_coeffs;
            svector<theory_var> m_vars;
            rational            m_coeff;
            ptr_vector<expr>    m_terms_to_internalize;
            internalize_state(ast_manager& m): m_terms(m) {}
            void reset() {
                m_terms.reset();
                m_coeffs.reset();
                m_coeff.reset();
                m_vars.reset();
                m_terms_to_internalize.reset();
            }
        };
        ptr_vector<internalize_state> m_internalize_states;
        unsigned                      m_internalize_head;

        class scoped_internalize_state {
            imp& m_imp;
            internalize_state& m_st;

            internalize_state& push_internalize(imp& i) {
                if (i.m_internalize_head == i.m_internalize_states.size()) {
                    i.m_internalize_states.push_back(alloc(internalize_state, i.m));
                }
                internalize_state& st = *i.m_internalize_states[i.m_internalize_head++];
                st.reset();
                return st;
            }
        public:
            scoped_internalize_state(imp& i): m_imp(i), m_st(push_internalize(i)) {}
            ~scoped_internalize_state() { --m_imp.m_internalize_head; }
            expr_ref_vector&     terms() { return m_st.m_terms; }                     
            vector<rational>&    coeffs() { return m_st.m_coeffs; }
            svector<theory_var>& vars() { return m_st.m_vars; }
            rational&            coeff() { return m_st.m_coeff; }
            ptr_vector<expr>&    terms_to_internalize() { return m_st.m_terms_to_internalize; }            
            void push(expr* e, rational c) { m_st.m_terms.push_back(e); m_st.m_coeffs.push_back(c); }
            void set_back(unsigned i) { 
                if (terms().size() == i + 1) return;
                terms()[i] = terms().back(); 
                coeffs()[i] = coeffs().back();
                terms().pop_back();
                coeffs().pop_back();
            }
        };
       
        typedef buffer<std::pair<rational, lean::var_index>> var_coeffs;
        struct delayed_def {
            vector<rational>    m_coeffs;
            svector<theory_var> m_vars;
            rational            m_coeff;
            theory_var          m_var;
            delayed_def(svector<theory_var> const& vars, vector<rational> const& coeffs, rational const& r, theory_var v):
                m_coeffs(coeffs), m_vars(vars), m_coeff(r), m_var(v) {}
        };

        svector<lean::var_index> m_theory_var2var_index;                         // translate from theory variables to lar vars
        var_coeffs               m_left_side;              // constraint left side
        mutable std::unordered_map<lean::var_index, rational> m_variable_values; // current model
        
        enum constraint_source {
            inequality_source,
            equality_source,
            definition_source,
            null_source
        };
        svector<constraint_source>                    m_constraint_sources;
        svector<literal>                              m_inequalities;    // asserted rows corresponding to inequality literals.
        svector<enode_pair>                           m_equalities;      // asserted rows corresponding to equalities.
        svector<theory_var>                           m_definitions;     // asserted rows corresponding to definitions

        bool                   m_delay_constraints;    // configuration
        svector<delayed_atom>  m_asserted_atoms;        
        app_ref_vector         m_delayed_terms;        
        svector<std::pair<theory_var, theory_var>> m_delayed_equalities;
        vector<delayed_def>    m_delayed_defs;
        expr*                  m_not_handled;
        ptr_vector<app>        m_underspecified;
        unsigned_vector        m_var_trail;

        // attributes for incremental version:
        u_map<lp::bound*>      m_bool_var2bound;
        vector<ptr_vector<lp::bound> > m_bounds;
        unsigned_vector        m_bounds_trail;
        unsigned               m_asserted_qhead;

        struct var_value_eq {
            imp & m_th;
            var_value_eq(imp & th):m_th(th) {}
            bool operator()(theory_var v1, theory_var v2) const { return m_th.get_value(v1) == m_th.get_value(v2) && m_th.is_int(v1) == m_th.is_int(v2); }
        };
        struct var_value_hash {
            imp & m_th;
            var_value_hash(imp & th):m_th(th) {}
            unsigned operator()(theory_var v) const { return m_th.get_value(v).hash(); }
        };
        int_hashtable<var_value_hash, var_value_eq>   m_model_eqs;


        svector<scope>         m_scopes;
        lp::stats              m_stats;
        arith_factory*         m_factory;       
        scoped_ptr<lean::lar_solver> m_solver;
        resource_limit         m_resource_limit;


        context& ctx() const { return th.get_context(); }
        theory_id get_id() const { return th.get_id(); }
        bool is_int(theory_var v) const {  return is_int(get_enode(v));  }
        bool is_int(enode* n) const { return a.is_int(n->get_owner()); }
        enode* get_enode(theory_var v) const { return th.get_enode(v); }
        enode* get_enode(expr* e) const { return ctx().get_enode(e); }

        void init_solver() {
            m_solver = alloc(lean::lar_solver); 
            m_theory_var2var_index.reset();
            m_solver->settings().set_resource_limit(m_resource_limit);
            reset_variable_values();
            //m_solver->settings().set_ostream(0);
        }

        void found_not_handled(expr* n) {
            m_not_handled = n;
            if (is_app(n) && is_underspecified(to_app(n))) {
                m_underspecified.push_back(to_app(n));
            }
            TRACE("arith", tout << "Unhandled: " << mk_pp(n, m) << "\n";);
        }

        bool is_numeral(expr* term, rational& r) {
            rational mul(1);
            do {
                if (a.is_numeral(term, r)) {
                    r *= mul;
                    return true;
                }
                if (a.is_uminus(term, term)) {
                    mul.neg();
                    continue;
                }
                if (a.is_to_real(term, term)) {
                    continue;
                }                
                return false;
            }
            while (false);
            return false;
        }

        void linearize_term(expr* term, scoped_internalize_state& st) {
            st.push(term, rational::one());
            linearize(st);
        } 
        
        void linearize_ineq(expr* lhs, expr* rhs, scoped_internalize_state& st) {
            st.push(lhs, rational::one());
            st.push(rhs, rational::minus_one());
            linearize(st);
        }
        
        void linearize(scoped_internalize_state& st) { 
            expr_ref_vector & terms = st.terms();
            svector<theory_var>& vars = st.vars();
            vector<rational>& coeffs = st.coeffs();
            rational& coeff = st.coeff();
            rational r;
            expr* n1, *n2;
            unsigned index = 0;
            while (index < terms.size()) {
                SASSERT(index >= vars.size());
                expr* n = terms[index].get();
                st.terms_to_internalize().push_back(n);
                if (a.is_add(n)) {
                    unsigned sz = to_app(n)->get_num_args();
                    for (unsigned i = 0; i < sz; ++i) {
                        st.push(to_app(n)->get_arg(i), coeffs[index]);
                    }
                    st.set_back(index);
                }
                else if (a.is_sub(n)) {
                    unsigned sz = to_app(n)->get_num_args();
                    terms[index] = to_app(n)->get_arg(0);                    
                    for (unsigned i = 1; i < sz; ++i) {
                        st.push(to_app(n)->get_arg(i), -coeffs[index]);
                    }
                }
                else if (a.is_mul(n, n1, n2) && is_numeral(n1, r)) {
                    coeffs[index] *= r;
                    terms[index] = n2;
                    st.terms_to_internalize().push_back(n1);
                }
                else if (a.is_mul(n, n1, n2) && is_numeral(n2, r)) {
                    coeffs[index] *= r;
                    terms[index] = n1;
                    st.terms_to_internalize().push_back(n2);
                }
                else if (a.is_numeral(n, r)) {
                    coeff += coeffs[index]*r;
                    ++index;
                }
                else if (a.is_uminus(n, n1)) {
                    coeffs[index].neg();
                    terms[index] = n1;
                }
                else if (is_app(n) && a.get_family_id() == to_app(n)->get_family_id()) {
                    app* t = to_app(n);
                    found_not_handled(n);
                    internalize_args(t);
                    mk_enode(t);
                    theory_var v = mk_var(n);
                    coeffs[vars.size()] = coeffs[index];
                    vars.push_back(v);
                    ++index;
                }
                else {
                    if (is_app(n)) {
                        internalize_args(to_app(n));
                    }
                    if (a.is_int(n)) {
                        found_not_handled(n);
                    }
                    theory_var v = mk_var(n);
                    coeffs[vars.size()] = coeffs[index];
                    vars.push_back(v);
                    ++index;
                }
            }
            for (unsigned i = st.terms_to_internalize().size(); i > 0; ) {
                --i;
                expr* n = st.terms_to_internalize()[i];
                if (is_app(n)) {
                    mk_enode(to_app(n));
                }
            }
            st.terms_to_internalize().reset();
        }

        void internalize_args(app* t) {
            for (unsigned i = 0; reflect(t) && i < t->get_num_args(); ++i) {
                if (!ctx().e_internalized(t->get_arg(i))) {
                    ctx().internalize(t->get_arg(i), false);
                }
            }
        }

        enode * mk_enode(app * n) {
            if (ctx().e_internalized(n)) {
                return get_enode(n);
            }
            else {
                return ctx().mk_enode(n, !reflect(n), false, enable_cgc_for(n));       
            }
        }

        bool enable_cgc_for(app * n) const {
            // Congruence closure is not enabled for (+ ...) and (* ...) applications.
            return !(n->get_family_id() == get_id() && (n->get_decl_kind() == OP_ADD || n->get_decl_kind() == OP_MUL));
        }


        void mk_clause(literal l1, literal l2, unsigned num_params, parameter * params) {
            ctx().mk_th_axiom(get_id(), l1, l2, num_params, params);
    }

        void mk_clause(literal l1, literal l2, literal l3, unsigned num_params, parameter * params) {
            ctx().mk_th_axiom(get_id(), l1, l2, l3, num_params, params);
        }

        bool is_underspecified(app* n) const {
            if (n->get_family_id() == get_id()) {
                switch (n->get_decl_kind()) {
                case OP_DIV:
                case OP_IDIV:
                case OP_REM:
                case OP_MOD:
                    return true;
                default:
                    break;
                }
            }
            return false;
        }

        bool reflect(app* n) const {
            return m_params.m_arith_reflect || is_underspecified(n);          
        }

        theory_var mk_var(expr* n, bool internalize = true) {
            if (!ctx().e_internalized(n)) {
                ctx().internalize(n, false);                
            }
            enode* e = get_enode(n);
            theory_var v;
            if (!th.is_attached_to_var(e)) {
                v = th.mk_var(e);
                SASSERT(m_bounds.size() <= static_cast<unsigned>(v) || m_bounds[v].empty());
                if (m_bounds.size() <= static_cast<unsigned>(v)) {
                    m_bounds.push_back(ptr_vector<lp::bound>());
                }
                ctx().attach_th_var(e, &th, v);
            }
            else {
                v = e->get_th_var(get_id());                
            }
            SASSERT(null_theory_var != v);
            return v;
        }
        
        lean::var_index get_var_index(theory_var v) {
            lean::var_index result = UINT_MAX;
            if (m_theory_var2var_index.size() > static_cast<unsigned>(v)) {
                result = m_theory_var2var_index[v];
            }
            if (result == UINT_MAX) {
                std::ostringstream s;
                s << "v" << v;
                result = m_solver->add_var(s.str());
                m_theory_var2var_index.setx(v, result, UINT_MAX);
                m_var_trail.push_back(v);
            }
            return result;
        }
        
        void init_left_side(scoped_internalize_state& st) {
            SASSERT(all_zeros(m_columns));
            svector<theory_var> const& vars = st.vars();
            vector<rational> const& coeffs = st.coeffs();
            for (unsigned i = 0; i < vars.size(); ++i) {
                theory_var var = vars[i];
                rational const& coeff = coeffs[i];
                if (m_columns.size() <= static_cast<unsigned>(var)) {
                    m_columns.setx(var, coeff, rational::zero());
                }
                else {
                    m_columns[var] += coeff;
                }                
            }
            m_left_side.reset();
            // reset the coefficients after they have been used.
            for (unsigned i = 0; i < vars.size(); ++i) {
                theory_var var = vars[i];
                rational const& r = m_columns[var];
                if (!r.is_zero()) {
                    m_left_side.push_back(std::make_pair(r, get_var_index(var)));
                    m_columns[var].reset();                    
                }
            }
            SASSERT(all_zeros(m_columns));
        }
        
        bool all_zeros(vector<rational> const& v) const {
            for (unsigned i = 0; i < v.size(); ++i) {
                if (!v[i].is_zero()) {
                    return false;
                }
            }
            return true;
        }
        
        void add_eq_constraint(lean::constraint_index index, enode* n1, enode* n2) {
            m_constraint_sources.setx(index, equality_source, null_source);
            m_equalities.setx(index, enode_pair(n1, n2), enode_pair(0, 0));
            ++m_stats.m_add_rows;
        }
        
        void add_ineq_constraint(lean::constraint_index index, literal lit) {
            m_constraint_sources.setx(index, inequality_source, null_source);
            m_inequalities.setx(index, lit, null_literal);
            ++m_stats.m_add_rows;
            TRACE("arith", m_solver->print_constraint(index, tout); tout << "\n";);
        }
        
        void add_def_constraint(lean::constraint_index index, theory_var v) {
            m_constraint_sources.setx(index, definition_source, null_source);
            m_definitions.setx(index, v, null_theory_var);
            ++m_stats.m_add_rows;
        }

        void internalize_eq(delayed_def const& d) {
            scoped_internalize_state st(*this);
            st.vars().append(d.m_vars);
            st.coeffs().append(d.m_coeffs);            
            init_left_side(st);
            add_def_constraint(m_solver->add_constraint(m_left_side, lean::EQ, -d.m_coeff), d.m_var);
        }
        
        void internalize_eq(theory_var v1, theory_var v2) {
                  
            enode* n1 = get_enode(v1);
            enode* n2 = get_enode(v2);
            scoped_internalize_state st(*this);
            st.vars().push_back(v1);
            st.vars().push_back(v2);
            st.coeffs().push_back(rational::one());
            st.coeffs().push_back(rational::minus_one());
            init_left_side(st);
            add_eq_constraint(m_solver->add_constraint(m_left_side, lean::EQ, rational::zero()), n1, n2);
            TRACE("arith", 
                  tout << "v" << v1 << " = " << "v" << v2 << ": "
                  << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << "\n";);
        }

        void internalize_atom2(expr* atom, bool_var bv, bool is_true) {
            TRACE("arith", tout << mk_pp(atom, m) << " " << is_true << "\n";);
            expr* n1, *n2;
            lean::lconstraint_kind k = lean::EQ;

#if 0
            theory_var v = null_theory_var;
            scoped_internalize_state st(*this);
            rational right_side;
            if (a.is_le(atom, n1, n2) && is_numeral(n2, right_side) && is_app(n1)) {
                v = internalize_def(to_app(n1), st);
                k = is_true ? lean::LE : lean::GT;
            }
            else if (a.is_ge(atom, n1, n2) && is_numeral(n2, right_side) && is_app(n1)) {
                v = internalize_def(to_app(n1), st);
                k = is_true ? lean::GE : lean::LT;
            }    
            else {
                TRACE("arith", tout << "Could not internalize " << mk_pp(atom, m) << "\n";);
                found_not_handled(atom);
                return;
            }
            TRACE("arith", tout << "Internalized " << mk_pp(atom, m) << "\n";);
            if (!is_unit_var(st)) {
                init_left_side(st);
                add_def_constraint(m_solver->add_constraint(m_left_side, lean::EQ, -st.coeff()), v);
            }
            m_left_side.reset();
            m_left_side.push_back(std::make_pair(rational::one(), get_var_index(v)));
            add_ineq_constraint(m_solver->add_constraint(m_left_side, k, right_side), literal(bv, !is_true));
#else
            if (a.is_le(atom, n1, n2)){
                k = is_true ? lean::LE : lean::GT;
            }
            else if (a.is_ge(atom, n1, n2)) {
                k = is_true ? lean::GE : lean::LT;
            }
            else if (a.is_is_int(atom)) {
                found_not_handled(atom);
                return;
            }
            else {
                UNREACHABLE();
            }
            scoped_internalize_state st(*this);
            linearize_ineq(n1, n2, st);
            init_left_side(st);
            rational right_side = -st.coeff();

            SASSERT(m_left_side.size() > 0);
            if (m_left_side.size() > 0) {
                add_ineq_constraint(m_solver->add_constraint(m_left_side, k, right_side), literal(bv, !is_true));
            }
            else {
                // really should check if equality is true or false. 
                // if equality is false, then we have contradiction here.
                TRACE("arith", tout << "Ignoring inequality\n";);                
            }
#endif
        }


        void del_bounds(unsigned old_size) {
            for (unsigned i = m_bounds_trail.size(); i > old_size; ) {
                --i;
                unsigned v = m_bounds_trail[i];
                dealloc(m_bounds[v].back());
                m_bounds[v].pop_back();
                        
            }
            m_bounds_trail.shrink(old_size);
        }
       
        bool is_unit_var(scoped_internalize_state& st) {
            return st.coeff().is_zero() && st.vars().size() == 1 && st.coeffs()[0].is_one();
        }

        theory_var internalize_def(app* term, scoped_internalize_state& st) {
            linearize_term(term, st);
            if (is_unit_var(st)) {
                return st.vars()[0];
            }
            else {
                theory_var v = mk_var(term);
                SASSERT(null_theory_var != v);
                st.coeffs().resize(st.vars().size() + 1);
                st.coeffs()[st.vars().size()] = rational::minus_one();
                st.vars().push_back(v);
                return v;
            }
        }

        // term - v = 0
        theory_var internalize_def(app* term) {
            scoped_internalize_state st(*this);
            theory_var v = internalize_def(term, st);
            if (is_unit_var(st)) {
                return st.vars()[0];
            }
            else {
                TRACE("arith", tout << "v" << v << " := " << mk_pp(term, m) << "\n";);
                init_left_side(st);
                add_def_constraint(m_solver->add_constraint(m_left_side, lean::EQ, -st.coeff()), v);
                return v;
            }
        }
        

    public:
        imp(theory_lra& th, ast_manager& m, theory_arith_params& p): 
            th(th), m(m), m_params(p), a(m), 
            m_arith_eq_adapter(th, p, a),
            m_internalize_head(0),
            m_asserted_qhead(0), 
            m_delay_constraints(false), 
            m_delayed_terms(m),
            m_not_handled(0),
            m_model_eqs(DEFAULT_HASHTABLE_INITIAL_CAPACITY, var_value_hash(*this), var_value_eq(*this)),
            m_resource_limit(*this) {
            init_solver();
        }
        
        ~imp() {
            del_bounds(0);
            std::for_each(m_internalize_states.begin(), m_internalize_states.end(), delete_proc<internalize_state>());
        }
        
        bool internalize_atom(app * atom, bool gate_ctx) {
            SASSERT(!ctx().b_internalized(atom));

            bool_var bv = ctx().mk_bool_var(atom);
            ctx().set_var_theory(bv, get_id());
            expr* n1, *n2;
            rational r;
            lp::bound_kind k;
            theory_var v = null_theory_var;
            scoped_internalize_state st(*this);
            if (a.is_le(atom, n1, n2) && is_numeral(n2, r) && is_app(n1)) {
                v = internalize_def(to_app(n1), st);
                k = lp::upper_t;
            }
            else if (a.is_ge(atom, n1, n2) && is_numeral(n2, r) && is_app(n1)) {
                v = internalize_def(to_app(n1), st);
                k = lp::lower_t;
            }    
            else {
                TRACE("arith", tout << "Could not internalize " << mk_pp(atom, m) << "\n";);
                found_not_handled(atom);
                return true;
            }
            lp::bound* b = alloc(lp::bound, bv, v, r, k);
            m_bounds[v].push_back(b);
            m_bounds_trail.push_back(v);
            m_bool_var2bound.insert(bv, b);
            TRACE("arith", tout << "Internalized " << mk_pp(atom, m) << "\n";);
            if (!is_unit_var(st) && m_bounds[v].size() == 1) {
                if (m_delay_constraints) {
                    m_delayed_defs.push_back(delayed_def(st.vars(), st.coeffs(), st.coeff(), v));                    
                }
                else {
                    init_left_side(st);
                    add_def_constraint(m_solver->add_constraint(m_left_side, lean::EQ, -st.coeff()), v);
                }
            }
            return true;
        }
        
        bool internalize_term(app * term) {
            if (ctx().e_internalized(term) && th.is_attached_to_var(ctx().get_enode(term))) {
                // skip
            }
            else if (m_delay_constraints) {
                scoped_internalize_state st(*this);
                linearize_term(term, st);  // ensure that a theory_var was created.
                SASSERT(ctx().e_internalized(term));
                if(!th.is_attached_to_var(ctx().get_enode(term))) {
                    mk_var(term);
                }
                m_delayed_terms.push_back(term);
            }
            else {
                internalize_def(term);
            }
            return true;
        }
        
        void internalize_eq_eh(app * atom, bool_var) {
            expr* lhs, *rhs;
            VERIFY(m.is_eq(atom, lhs, rhs));
            enode * n1 = get_enode(lhs);
            enode * n2 = get_enode(rhs);
            if (n1->get_th_var(get_id()) != null_theory_var &&
                n2->get_th_var(get_id()) != null_theory_var &&
                n1 != n2) {
                TRACE("arith", tout << mk_pp(atom, m) << "\n";);
                m_arith_eq_adapter.mk_axioms(n1, n2);
            }
        }

        void assign_eh(bool_var v, bool is_true) {
            TRACE("arith", tout << mk_pp(ctx().bool_var2expr(v), m) << "\n";);
            m_asserted_atoms.push_back(delayed_atom(v, is_true));
        }

        void new_eq_eh(theory_var v1, theory_var v2) {
            if (m_delay_constraints) {
                m_delayed_equalities.push_back(std::make_pair(v1, v2));
            }
            else {
                // or internalize_eq(v1, v2);
                m_arith_eq_adapter.new_eq_eh(v1, v2);
            }
        }

        bool use_diseqs() const {
            return true;
        }

        void new_diseq_eh(theory_var v1, theory_var v2) {
            TRACE("arith", tout << "v" << v1 << " != " << "v" << v2 << "\n";);
            m_arith_eq_adapter.new_diseq_eh(v1, v2);
        }

        void push_scope_eh() {
            m_scopes.push_back(scope());
            scope& s = m_scopes.back();
            s.m_bounds_lim = m_bounds_trail.size();
            s.m_asserted_qhead = m_asserted_qhead;
            s.m_asserted_atoms_lim = m_asserted_atoms.size();
            s.m_delayed_terms_lim = m_delayed_terms.size();
            s.m_delayed_equalities_lim = m_delayed_equalities.size();
            s.m_delayed_defs_lim = m_delayed_defs.size();
            s.m_not_handled = m_not_handled;
            s.m_underspecified_lim = m_underspecified.size();
            s.m_var_trail_lim = m_var_trail.size();
            if (!m_delay_constraints) m_solver->push();
        }

        void pop_scope_eh(unsigned num_scopes) {
            if (num_scopes == 0) {
                return;
            }
            unsigned old_size = m_scopes.size() - num_scopes;
            del_bounds(m_scopes[old_size].m_bounds_lim);
            for (unsigned i = m_scopes[old_size].m_var_trail_lim; i < m_var_trail.size(); ++i) {
                m_theory_var2var_index[m_var_trail[i]] = UINT_MAX;
            }
            m_asserted_atoms.shrink(m_scopes[old_size].m_asserted_atoms_lim);
            m_delayed_terms.shrink(m_scopes[old_size].m_delayed_terms_lim);
            m_delayed_defs.shrink(m_scopes[old_size].m_delayed_defs_lim);
            m_delayed_equalities.shrink(m_scopes[old_size].m_delayed_equalities_lim);
            m_asserted_qhead = m_scopes[old_size].m_asserted_qhead;
            m_underspecified.shrink(m_scopes[old_size].m_underspecified_lim);
            m_var_trail.shrink(m_scopes[old_size].m_var_trail_lim);
            m_not_handled = m_scopes[old_size].m_not_handled;
            m_scopes.resize(old_size);            
            if (!m_delay_constraints) m_solver->pop(num_scopes);
        }

        void restart_eh() {
            m_arith_eq_adapter.restart_eh();
        }

        void relevant_eh(app* n) {
            TRACE("arith", tout << mk_pp(n, m) << "\n";);
            expr* n1, *n2;
            if (a.is_mod(n, n1, n2)) 
                mk_idiv_mod_axioms(n1, n2);
            else if (a.is_rem(n, n1, n2))
                mk_rem_axiom(n1, n2);
            else if (a.is_div(n, n1, n2)) 
                mk_div_axiom(n1, n2);
            else if (a.is_to_int(n)) 
                mk_to_int_axiom(n);
            else if (a.is_is_int(n))
                mk_is_int_axiom(n);            
        }

        //  n < 0 || rem(a, n) =  mod(a, n)
        // !n < 0 || rem(a, n) = -mod(a, n)
        void mk_rem_axiom(expr* dividend, expr* divisor) {
            expr_ref zero(a.mk_int(0), m);
            expr_ref rem(a.mk_rem(dividend, divisor), m);
            expr_ref mod(a.mk_mod(dividend, divisor), m);
            expr_ref mmod(a.mk_uminus(mod), m);
            literal dgez = mk_literal(a.mk_ge(divisor, zero));
            mk_axiom(~dgez, th.mk_eq(rem, mod,  false));
            mk_axiom( dgez, th.mk_eq(rem, mmod, false));                    
        }

        // q = 0 or q * (p div q) = p
        void mk_div_axiom(expr* p, expr* q) {
            if (a.is_zero(q)) return;
            literal eqz = th.mk_eq(q, a.mk_real(0), false);
            literal eq  = th.mk_eq(a.mk_mul(q, a.mk_div(p, q)), p, false);
            mk_axiom(eqz, eq);
        }

        // to_int (to_real x) = x
        // to_real(to_int(x)) <= x < to_real(to_int(x)) + 1
        void mk_to_int_axiom(app* n) {
            expr* x, *y;
            VERIFY (a.is_to_int(n, x));            
            if (a.is_to_real(x, y)) {
                mk_axiom(th.mk_eq(y, n, false));
            }
            else {
                expr_ref to_r(a.mk_to_real(n), m);
                expr_ref lo(a.mk_le(a.mk_sub(to_r, x), a.mk_real(0)), m);
                expr_ref hi(a.mk_ge(a.mk_sub(x, to_r), a.mk_real(1)), m);
                mk_axiom(mk_literal(lo));
                mk_axiom(~mk_literal(hi));
            }
        }

        // is_int(x) <=> to_real(to_int(x)) = x
        void mk_is_int_axiom(app* n) {
            expr* x;
            VERIFY(a.is_is_int(n, x));
            literal eq = th.mk_eq(a.mk_to_real(a.mk_to_int(x)), x, false);
            literal is_int = ctx().get_literal(n);
            mk_axiom(~is_int, eq);
            mk_axiom(is_int, ~eq);
        }

        void mk_idiv_mod_axioms(expr * p, expr * q) {
            if (a.is_zero(q)) {
                return;
            }
            // if q is zero, then idiv and mod are uninterpreted functions.
            expr_ref div(a.mk_idiv(p, q), m);
            expr_ref mod(a.mk_mod(p, q), m);
            expr_ref zero(a.mk_int(0), m);
            literal q_ge_0     = mk_literal(a.mk_ge(q, zero));
            literal q_le_0     = mk_literal(a.mk_le(q, zero));
            literal eqz        = th.mk_eq(q, zero, false);
            literal eq         = th.mk_eq(a.mk_add(a.mk_mul(q, div), mod), p, false);
            literal mod_ge_0   = mk_literal(a.mk_ge(mod, zero));
            // q >= 0 or p = (p mod q) + q * (p div q)
            // q <= 0 or p = (p mod q) + q * (p div q)
            // q >= 0 or (p mod q) >= 0
            // q <= 0 or (p mod q) >= 0
            // q <= 0 or (p mod q) <  q
            // q >= 0 or (p mod q) < -q
            mk_axiom(q_ge_0, eq);
            mk_axiom(q_le_0, eq);
            mk_axiom(q_ge_0, mod_ge_0);
            mk_axiom(q_le_0, mod_ge_0);
            mk_axiom(q_le_0, ~mk_literal(a.mk_ge(a.mk_sub(mod, q), zero)));
            mk_axiom(q_ge_0, ~mk_literal(a.mk_ge(a.mk_add(mod, q), zero)));
            rational k;
            if (m_params.m_arith_enum_const_mod && a.is_numeral(q, k) && 
                k.is_pos() && k < rational(8)) {
                unsigned _k = k.get_unsigned();
                literal_buffer lits;
                for (unsigned j = 0; j < _k; ++j) {
                    literal mod_j = th.mk_eq(mod, a.mk_int(j), false);
                    lits.push_back(mod_j);
                    ctx().mark_as_relevant(mod_j);
                }
                ctx().mk_th_axiom(get_id(), lits.size(), lits.begin());                
            }            
        }

        void mk_axiom(literal l) {
            ctx().mk_th_axiom(get_id(), false_literal, l);
            if (ctx().relevancy()) {
                ctx().mark_as_relevant(l);
            }
        }

        void mk_axiom(literal l1, literal l2) {
            if (l1 == false_literal) {
                mk_axiom(l2);
                return;
            }
            ctx().mk_th_axiom(get_id(), l1, l2);
            if (ctx().relevancy()) {
                ctx().mark_as_relevant(l1);
                expr_ref e(m);
                ctx().literal2expr(l2, e);
                ctx().add_rel_watch(~l1, e);
            }
        }

        void mk_axiom(literal l1, literal l2, literal l3) {
            ctx().mk_th_axiom(get_id(), l1, l2, l3);
            if (ctx().relevancy()) {
                expr_ref e(m);
                ctx().mark_as_relevant(l1);
                ctx().literal2expr(l2, e);
                ctx().add_rel_watch(~l1, e);
                ctx().literal2expr(l3, e);
                ctx().add_rel_watch(~l2, e);
            }
        }

        literal mk_literal(expr* e) {
            expr_ref pinned(e, m);
            if (!ctx().e_internalized(e)) {
                ctx().internalize(e, false);
            }
            return ctx().get_literal(e);
        }


        void init_search_eh() {
            m_arith_eq_adapter.init_search_eh();
        }


        bool can_get_value(theory_var v) const {
            return 
                (v != null_theory_var) &&
                (v < static_cast<theory_var>(m_theory_var2var_index.size())) && 
                (UINT_MAX != m_theory_var2var_index[v]) && 
                m_variable_values.count(v) > 0;
        }

        rational const& get_value(theory_var v) const {
            if (!can_get_value(v)) return rational::zero();
            lean::var_index vi = m_theory_var2var_index[v];
            return m_variable_values[vi];        
        }

        void init_variable_values() {
            if (m_variable_values.size() == 0 && m_solver.get()) {
                m_solver->get_model(m_variable_values);
            }
        }

        void reset_variable_values() {
            m_variable_values.clear();
        }

        bool assume_eqs() {        
            svector<lean::var_index> vars;
            theory_var sz = static_cast<theory_var>(m_theory_var2var_index.size())
;
            for (theory_var v = 0; v < sz; ++v) {
                if (th.is_relevant_and_shared(get_enode(v))) { 
                    vars.push_back(m_theory_var2var_index[v]);
                }
            }
            if (vars.empty()) {
                return false;
            }
            m_solver->random_update(vars.size(), vars.c_ptr());
            init_variable_values();
            m_model_eqs.reset();
            TRACE("arith", display(tout););
            
            int start = ctx().get_random_value();
            for (theory_var i = 0; i < sz; ++i) {
                theory_var v = (i + start) % sz;
                enode* n1 = get_enode(v);
                if (!th.is_relevant_and_shared(n1)) {                    
                    continue;
                }
                if (!can_get_value(v)) {
                    continue;
                }
                theory_var other = m_model_eqs.insert_if_not_there(v);
                if (other == v) {
                    continue;
                }
                enode* n2 = get_enode(other);
                if (n1->get_root() != n2->get_root()) {
                    TRACE("arith", tout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << "\n";);
                    std::cout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << "\n";
                    std::cout << m_theory_var2var_index[v] << " = " << m_theory_var2var_index[other] << "\n";
                    th.assume_eq(n1, n2);
                    return true;
                }
            }
            return false;
        }

        void profile_solver() {
            for (unsigned i = 0; i < 100; ++i) {
                init_solver();
                for (unsigned i = 0; i < m_asserted_atoms.size(); ++i) {
                    bool_var bv = m_asserted_atoms[i].m_bv;
                    assert_bound(bv, m_asserted_atoms[i].m_is_true, *m_bool_var2bound.find(bv));
                }
                for (unsigned i = 0; i < m_delayed_terms.size(); ++i) {
                    internalize_def(m_delayed_terms[i].get());
                }
                for (unsigned i = 0; i < m_delayed_defs.size(); ++i) {
                    delayed_def const& dd = m_delayed_defs[i];
                    internalize_eq(dd);
                }
                for (unsigned i = 0; i < m_delayed_equalities.size(); ++i) {
                    std::pair<theory_var, theory_var> const& eq = m_delayed_equalities[i];
                    internalize_eq(eq.first, eq.second);
                }
                make_feasible();
            }
        }

        bool has_delayed_constraints() const {
            return !(m_asserted_atoms.empty() && m_delayed_terms.empty() && m_delayed_equalities.empty());
        }

        final_check_status final_check_eh() {
            if (!has_delayed_constraints()) {
                return FC_DONE;
            }
            //profile_solver();
            if (m_delay_constraints) {
                init_solver();
                for (unsigned i = 0; i < m_asserted_atoms.size(); ++i) {
                    bool_var bv = m_asserted_atoms[i].m_bv;
                    assert_bound(bv, m_asserted_atoms[i].m_is_true, *m_bool_var2bound.find(bv));
                }
                for (unsigned i = 0; i < m_delayed_terms.size(); ++i) {
                    internalize_def(m_delayed_terms[i].get());
                }
                for (unsigned i = 0; i < m_delayed_defs.size(); ++i) {
                    internalize_eq(m_delayed_defs[i]);
                }
                for (unsigned i = 0; i < m_delayed_equalities.size(); ++i) {
                    std::pair<theory_var, theory_var> const& eq = m_delayed_equalities[i];
                    internalize_eq(eq.first, eq.second);
                }
            }
            lbool is_sat = make_feasible();
            switch (is_sat) {
            case l_true:
                if (assume_eqs()) {
                    return FC_CONTINUE;
                }
                if (m_not_handled != 0) {                    
                    return FC_GIVEUP;
                }
                return FC_DONE;
            case l_false:
                set_conflict();
                return FC_CONTINUE;
            case l_undef:
                return m.canceled() ? FC_CONTINUE : FC_GIVEUP;
            default:
                UNREACHABLE();
                break;
            }
            return FC_GIVEUP;
        }


        /**
           \brief We must redefine this method, because theory of arithmetic contains
           underspecified operators such as division by 0.
           (/ a b) is essentially an uninterpreted function when b = 0.
           Thus, 'a' must be considered a shared var if it is the child of an underspecified operator.

           if merge(a / b, x + y) and a / b is root, then x + y become shared and all z + u in equivalence class of x + y.
                      

           TBD: when the set of underspecified subterms is small, compute the shared variables below it.
                Recompute the set if there are merges that invalidate it.
                Use the set to determine if a variable is shared.
        */
        bool is_shared(theory_var v) const {
            if (m_underspecified.empty()) {
                return false;
            }
            enode * n      = get_enode(v);
            enode * r      = n->get_root();
            unsigned usz   = m_underspecified.size();
            TRACE("shared", tout << ctx().get_scope_level() << " " <<  v << " " << r->get_num_parents() << "\n";);
            if (r->get_num_parents() > 2*usz) {
                for (unsigned i = 0; i < usz; ++i) {
                    app* u = m_underspecified[i];
                    unsigned sz = u->get_num_args();
                    for (unsigned j = 0; j < sz; ++j) {
                        if (ctx().get_enode(u->get_arg(j))->get_root() == r) {
                            return true;
                        }
                    }
                }
            }
            else {
                enode_vector::const_iterator it  = r->begin_parents();
                enode_vector::const_iterator end = r->end_parents();
                for (; it != end; ++it) {
                    enode * parent = *it;
                    if (is_underspecified(parent->get_owner())) {
                        return true;
                    }
                }
            }
            return false;
        }


        bool can_propagate() {
            if (ctx().at_base_level() && has_delayed_constraints()) {
                // we could add the delayed constraints here directly to the tableau instead of using bounds variables.
            }
            return m_asserted_atoms.size() > m_asserted_qhead;
        }

        void propagate() {
            if (!can_propagate()) {
                return;
            }
            while (m_asserted_qhead < m_asserted_atoms.size() && !ctx().inconsistent()) {
                bool_var bv  = m_asserted_atoms[m_asserted_qhead].m_bv;
                bool is_true = m_asserted_atoms[m_asserted_qhead].m_is_true;
                lp::bound& b = *m_bool_var2bound.find(bv);
                
                propagate_bound(bv, is_true, b);
                
                if (!m_delay_constraints) {
                    assert_bound(bv, is_true, b);
                }

                ++m_asserted_qhead;
            }
            if (m_delay_constraints || ctx().inconsistent()) {
                return;
            }
            switch (make_feasible()) {
            case l_false:
                TRACE("arith", tout << "propagation conflict\n";);
                set_conflict();
                break;
            case l_true:
                break;
            case l_undef:
                break;
            }
        }


        // for glb lo': lo' < lo:
        //   lo <= x -> lo' <= x 
        //   lo <= x -> ~(x <= lo')
        // for lub hi': hi' > hi
        //   x <= hi -> x <= hi'
        //   x <= hi -> ~(x >= hi')

        void propagate_bound(bool_var bv, bool is_true, lp::bound& b) {
            lp::bound_kind k = b.get_bound_kind();
            theory_var v = b.get_var();
            inf_rational val = b.get_value(is_true);
            ptr_vector<lp::bound> const& bounds = m_bounds[v];
            SASSERT(!bounds.empty());
            if (bounds.size() == 1) return;

            literal lit1(bv, !is_true);
            literal lit2 = null_literal;
            bool find_glb = (is_true == (k == lp::lower_t));
            if (find_glb) {
                rational glb;
                lp::bound* lb = 0;
                for (unsigned i = 0; i < bounds.size(); ++i) {
                    lp::bound* b2 = bounds[i];
                    if (b2 == &b) continue;
                    rational const& val2 = b2->get_value();
                    if ((is_true ? val2 < val : val2 <= val) && (!lb || glb < val2)) {
                        lb = b2;
                        glb = val2;
                    }
                }
                if (!lb) return;
                bool sign = lb->get_bound_kind() != lp::lower_t;
                lit2 = literal(lb->get_bv(), sign);                    
            }
            else {
                rational lub;
                lp::bound* ub = 0;
                for (unsigned i = 0; i < bounds.size(); ++i) {
                    lp::bound* b2 = bounds[i];
                    if (b2 == &b) continue;
                    rational const& val2 = b2->get_value();
                    if ((is_true ? val < val2 : val <= val2) && (!ub || val2 < lub)) {
                        ub = b2;
                        lub = val2;
                    }
                }
                if (!ub) return;
                bool sign = ub->get_bound_kind() != lp::upper_t;
                lit2 = literal(ub->get_bv(), sign);
            }
            TRACE("arith", 
                  ctx().display_literal_verbose(tout, lit1);
                  ctx().display_literal_verbose(tout << " => ", lit2);
                  tout << "\n";);
            parameter coeffs[3] = { parameter(symbol("farkas")), parameter(rational(1)), parameter(rational(1)) };
            ctx().assign(
                lit2, ctx().mk_justification(
                    theory_propagation_justification(
                        get_id(), ctx().get_region(), 1, &lit1, lit2, 3, coeffs)));
            ++m_stats.m_bounds_propagations;
        }

        void assert_bound(bool_var bv, bool is_true, lp::bound& b) {
            scoped_internalize_state st(*this);
            st.vars().push_back(b.get_var());
            st.coeffs().push_back(rational::one());
            init_left_side(st);
            lean::lconstraint_kind k = lean::EQ;
            switch (b.get_bound_kind()) {
            case lp::lower_t:
                k = is_true ? lean::GE : lean::LT;
                break;
            case lp::upper_t:
                k = is_true ? lean::LE : lean::GT;
                break;
            }         
            if (k == lean::LT || k == lean::LE) {
                ++m_stats.m_assert_lower;
            }
            else {
                ++m_stats.m_assert_upper;
            }
            add_ineq_constraint(m_solver->add_constraint(m_left_side, k, b.get_value()), literal(bv, !is_true));
        }

        lbool make_feasible() {
            reset_variable_values();
            TRACE("arith", display(tout););
            stopwatch sw;
            sw.start();
            lean::lp_status status = m_solver->check();
            sw.stop();
            std::cout << status << " " << sw.get_seconds() << "\n";
            m_stats.m_num_iterations += m_solver->settings().st().m_total_iterations;
            //m_stats.m_num_iterations_with_no_progress += m_solver->settings().st().m_iters_with_no_cost_growing;

            switch (status) {
            case lean::lp_status::INFEASIBLE:
                return l_false;
            case lean::lp_status::FEASIBLE:
            case lean::lp_status::OPTIMAL:
                SASSERT(m_solver->all_constraints_hold());
                return l_true;
            case lean::lp_status::TIME_EXHAUSTED:
                
            default:
                TRACE("arith", tout << "status treated as inconclusive: " << status << "\n";);
                // TENTATIVE_UNBOUNDED, UNBOUNDED, TENTATIVE_DUAL_UNBOUNDED, DUAL_UNBOUNDED, 
                // FLOATING_POINT_ERROR, TIME_EXAUSTED, ITERATIONS_EXHAUSTED, EMPTY, UNSTABLE
                return l_undef;
            }
        }

        buffer<std::pair<rational, lean::constraint_index>> m_evidence;
        literal_vector      m_core;
        svector<enode_pair> m_eqs;

        void set_conflict() {
            m_eqs.reset();
            m_core.reset();
            m_evidence.reset();
            m_solver->get_infeasibility_evidence(m_evidence);
            TRACE("arith", display_evidence(tout, m_evidence); );
            for (auto const& ev : m_evidence) {
                if (ev.first.is_zero()) { 
                    continue;
                }
                unsigned idx = ev.second;
                switch (m_constraint_sources[idx]) {
                case inequality_source: {
                    literal lit = m_inequalities[idx];
                    SASSERT(lit != null_literal);
                    m_core.push_back(lit);
                    break;
                }
                case equality_source: {
                    SASSERT(m_equalities[idx].first  != nullptr);
                    SASSERT(m_equalities[idx].second != nullptr);
                    m_eqs.push_back(m_equalities[idx]);          
                    break;
                }
                case definition_source: {
                    // skip definitions (these are treated as hard constraints)
                    break;
                }
                default:
                    UNREACHABLE();
                }
            }
            ctx().set_conflict(
                ctx().mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx().get_region(), 
                        m_core.size(), m_core.c_ptr(), 
                        m_eqs.size(), m_eqs.c_ptr(), 0, 0)));
        }

        justification * why_is_diseq(theory_var v1, theory_var v2) {
            return 0;
        }

        void reset_eh() {
            m_arith_eq_adapter.reset_eh();
            m_solver = 0;
            m_not_handled = nullptr;
            del_bounds(0);
            m_asserted_qhead  = 0;
            m_scopes.reset();
            m_stats.reset();
        }

        void init_model(model_generator & mg) {
            init_variable_values();
            m_factory = alloc(arith_factory, m);
            mg.register_factory(m_factory);
            TRACE("arith", display(tout););
        }

        model_value_proc * mk_value(enode * n, model_generator & mg) {
            theory_var v = n->get_th_var(get_id());
            return alloc(expr_wrapper_proc, m_factory->mk_value(get_value(v), is_int(n)));
        }

        bool get_value(enode* n, expr_ref& r) {
            theory_var v = n->get_th_var(get_id());            
            if (can_get_value(v)) {
                r = a.mk_numeral(get_value(v), is_int(n));
                return true;
            }
            else {
                return false;
            }
        }    

        bool validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const {
            SASSERT(v1 != null_theory_var);
            SASSERT(v2 != null_theory_var);
            return (get_value(v1) == get_value(v2)) == is_true;
        }

        void display(std::ostream & out) const {
            if (m_solver) {
                m_solver->print_constraints(out);
            }
            unsigned nv = th.get_num_vars();
            for (unsigned v = 0; v < nv; ++v) {
                out << "v" << v;
                if (can_get_value(v)) out << ", value: " << get_value(v);                
                out << ", shared: " << ctx().is_shared(get_enode(v)) 
                    << ", rel: " << ctx().is_relevant(get_enode(v)) 
                    << ", def: "; th.display_var_flat_def(out, v) << "\n";
            }
        }

        void display_evidence(std::ostream& out, buffer<std::pair<rational, lean::constraint_index>> const& evidence) {
            for (auto const& ev : evidence) {
                expr_ref e(m);
                SASSERT(!ev.first.is_zero()); 
                if (ev.first.is_zero()) { 
                    continue;
                }
                unsigned idx = ev.second;
                switch (m_constraint_sources[idx]) {
                case inequality_source: 
                    ctx().literal2expr(m_inequalities[idx], e);
                    out << e << "\n";
                    break;
                case equality_source: 
                    out << mk_pp(m_equalities[idx].first->get_owner(), m) << " = " 
                        << mk_pp(m_equalities[idx].second->get_owner(), m) << "\n"; 
                    break;
                case definition_source: {
                    theory_var v = m_definitions[idx];
                    out << "def: v" << v << " := " << mk_pp(th.get_enode(v)->get_owner(), m) << "\n";
                    break;
                }
                }
            }
            for (auto const& ev : evidence) {
                m_solver->print_constraint(ev.second, out << ev.first << ": "); out << "\n";
            }
        }

        void collect_statistics(::statistics & st) const {
            m_arith_eq_adapter.collect_statistics(st);
            st.update("arith-lower", m_stats.m_assert_lower);
            st.update("arith-upper", m_stats.m_assert_upper);
            st.update("arith-rows", m_stats.m_add_rows);
            st.update("arith-propagations", m_stats.m_bounds_propagations);
            st.update("arith-iterations", m_stats.m_num_iterations);
            st.update("arith-plateau-iterations", m_stats.m_num_iterations_with_no_progress);
        }        
    };
    
    theory_lra::theory_lra(ast_manager& m, theory_arith_params& p):
        theory(m.get_family_id("arith")) {
        m_imp = alloc(imp, *this, m, p);
    }    
    theory_lra::~theory_lra() {
        dealloc(m_imp);
    }   
    theory* theory_lra::mk_fresh(context* new_ctx) {
        return alloc(theory_lra, new_ctx->get_manager(), new_ctx->get_fparams());
    }
    void theory_lra::init(context * ctx) {
        theory::init(ctx);
    }
    bool theory_lra::internalize_atom(app * atom, bool gate_ctx) {
        return m_imp->internalize_atom(atom, gate_ctx);
    }
    bool theory_lra::internalize_term(app * term) {
        return m_imp->internalize_term(term);
    }
    void theory_lra::internalize_eq_eh(app * atom, bool_var v) {
        m_imp->internalize_eq_eh(atom, v);
    }
    void theory_lra::assign_eh(bool_var v, bool is_true) {
        m_imp->assign_eh(v, is_true);
    }
    void theory_lra::new_eq_eh(theory_var v1, theory_var v2) {
        m_imp->new_eq_eh(v1, v2);
    }
    bool theory_lra::use_diseqs() const {
        return m_imp->use_diseqs();
    }
    void theory_lra::new_diseq_eh(theory_var v1, theory_var v2) {
        m_imp->new_diseq_eh(v1, v2);
    }
    void theory_lra::push_scope_eh() {
        theory::push_scope_eh();
        m_imp->push_scope_eh();
    }
    void theory_lra::pop_scope_eh(unsigned num_scopes) {
        m_imp->pop_scope_eh(num_scopes);
        theory::pop_scope_eh(num_scopes);
    }
    void theory_lra::restart_eh() {
        m_imp->restart_eh();
    }
    void theory_lra::relevant_eh(app* e) {
        m_imp->relevant_eh(e);
    }
    void theory_lra::init_search_eh() {
        m_imp->init_search_eh();
    }
    final_check_status theory_lra::final_check_eh() {
        return m_imp->final_check_eh();
    }
    bool theory_lra::is_shared(theory_var v) const {
        return m_imp->is_shared(v);
    }
    bool theory_lra::can_propagate() {
        return m_imp->can_propagate();
    }
    void theory_lra::propagate() {
        m_imp->propagate();
    }
    justification * theory_lra::why_is_diseq(theory_var v1, theory_var v2) {
        return m_imp->why_is_diseq(v1, v2);
    }
    void theory_lra::reset_eh() {
        m_imp->reset_eh();
    }
    void theory_lra::init_model(model_generator & m) {
        m_imp->init_model(m);
    }
    model_value_proc * theory_lra::mk_value(enode * n, model_generator & mg) {
        return m_imp->mk_value(n, mg);
    }
    bool theory_lra::get_value(enode* n, expr_ref& r) {
        return m_imp->get_value(n, r);
    }
    bool theory_lra::validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const {
        return m_imp->validate_eq_in_model(v1, v2, is_true);
    }
    void theory_lra::display(std::ostream & out) const {
        m_imp->display(out);
    }
    void theory_lra::collect_statistics(::statistics & st) const {
        m_imp->collect_statistics(st);
    }



}
