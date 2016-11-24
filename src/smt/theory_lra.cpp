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
        unsigned m_num_factorizations;
        unsigned m_fixed_eqs;
        unsigned m_conflicts;
        unsigned m_bound_propagations1;
        unsigned m_bound_propagations2;
        unsigned m_assert_diseq;
        stats() { reset(); }
        void reset() {
            memset(this, 0, sizeof(*this));
        }
    };

    typedef optional<inf_rational> opt_inf_rational;


}

namespace smt {

    typedef ptr_vector<lp::bound> lp_bounds;
    
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
        int m_print_counter = 0;

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
       
        typedef std::vector<std::pair<rational, lean::var_index>> var_coeffs;
        struct delayed_def {
            vector<rational>    m_coeffs;
            svector<theory_var> m_vars;
            rational            m_coeff;
            theory_var          m_var;
            delayed_def(svector<theory_var> const& vars, vector<rational> const& coeffs, rational const& r, theory_var v):
                m_coeffs(coeffs), m_vars(vars), m_coeff(r), m_var(v) {}
        };

        svector<lean::var_index> m_theory_var2var_index;   // translate from theory variables to lar vars
        svector<theory_var>      m_var_index2theory_var;   // reverse map from lp_solver variables to theory variables  
        svector<theory_var>      m_term_index2theory_var;   // reverse map from lp_solver variables to theory variables  
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
        vector<lp_bounds>      m_bounds;
        unsigned_vector        m_unassigned_bounds;
        unsigned_vector        m_bounds_trail;
        unsigned               m_asserted_qhead;

        svector<std::pair<theory_var, theory_var> >       m_assume_eq_candidates; 
        unsigned                                          m_assume_eq_head;

        unsigned               m_num_conflicts;


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
        lp_bounds              m_new_bounds;


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
            TRACE("arith", literal lits[2]; lits[0] = l1; lits[1] = l2; ctx().display_literals_verbose(tout, 2, lits); tout << "\n";);
            // literal lits[2]; lits[0] = l1; lits[1] = l2; ctx().display_literals_verbose(std::cout, 2, lits); std::cout << "\n";
            ctx().mk_th_axiom(get_id(), l1, l2, num_params, params);
        }

        void mk_clause(literal l1, literal l2, literal l3, unsigned num_params, parameter * params) {
            TRACE("arith", literal lits[3]; lits[0] = l1; lits[1] = l2; lits[2] = l3; ctx().display_literals_verbose(tout, 3, lits); tout << "\n";);
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
                    m_bounds.push_back(lp_bounds());
                    m_unassigned_bounds.push_back(0);
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
                m_var_index2theory_var.setx(result, v, UINT_MAX);
                
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
            m_left_side.clear();
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

        void del_bounds(unsigned old_size) {
            for (unsigned i = m_bounds_trail.size(); i > old_size; ) {
                --i;
                unsigned v = m_bounds_trail[i];
                dealloc(m_bounds[v].back());
                m_bounds[v].pop_back();                        
            }
            m_bounds_trail.shrink(old_size);
        }

        void updt_unassigned_bounds(theory_var v, int inc) {
            ctx().push_trail(vector_value_trail<smt::context, unsigned, false>(m_unassigned_bounds, v));
            m_unassigned_bounds[v] += inc;
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
            linearize_term(term, st);
            if (is_unit_var(st)) {
                return st.vars()[0];
            }
            else {
                init_left_side(st);
                theory_var v = mk_var(term);
                lean::var_index vi = m_theory_var2var_index.get(v, UINT_MAX);
                if (vi == UINT_MAX) {
                    vi = m_solver->add_term(m_left_side, st.coeff());
                    m_theory_var2var_index.setx(v, vi, UINT_MAX);
                    if (m_solver->is_term(vi)) {
                        m_term_index2theory_var.setx(m_solver->adjust_term_index(vi), v, UINT_MAX);
                    }
                    else {
                        m_var_index2theory_var.setx(vi, v, UINT_MAX);
                    }
                    m_var_trail.push_back(v);
                    TRACE("arith", tout << "v" << v << " := " << mk_pp(term, m) << " slack: " << vi << " scopes: " << m_scopes.size() << "\n";
                          m_solver->print_term(m_solver->get_term(vi), tout); tout << "\n";);
                }
                return v;
            }
        }
        

    public:
        imp(theory_lra& th, ast_manager& m, theory_arith_params& p): 
            th(th), m(m), m_params(p), a(m), 
            m_arith_eq_adapter(th, p, a),
            m_internalize_head(0),
            m_delay_constraints(false), 
            m_delayed_terms(m),
            m_not_handled(0),
            m_asserted_qhead(0), 
            m_assume_eq_head(0),
            m_num_conflicts(0),
            m_model_eqs(DEFAULT_HASHTABLE_INITIAL_CAPACITY, var_value_hash(*this), var_value_eq(*this)),
            m_resource_limit(*this) {
            init_solver();
        }
        
        ~imp() {
            del_bounds(0);
            std::for_each(m_internalize_states.begin(), m_internalize_states.end(), delete_proc<internalize_state>());
        }
        
        bool internalize_atom(app * atom, bool gate_ctx) {
            if (m_delay_constraints) {
                return internalize_atom_lazy(atom, gate_ctx);
            }
            else {
                return internalize_atom_strict(atom, gate_ctx);
            }
        }

        bool internalize_atom_strict(app * atom, bool gate_ctx) {
            SASSERT(!ctx().b_internalized(atom));
            bool_var bv = ctx().mk_bool_var(atom);
            ctx().set_var_theory(bv, get_id());
            expr* n1, *n2;
            rational r;
            lp::bound_kind k;
            theory_var v = null_theory_var;
            if (a.is_le(atom, n1, n2) && is_numeral(n2, r) && is_app(n1)) {
                v = internalize_def(to_app(n1));
                k = lp::upper_t;
            }
            else if (a.is_ge(atom, n1, n2) && is_numeral(n2, r) && is_app(n1)) {
                v = internalize_def(to_app(n1));
                k = lp::lower_t;
            }    
            else {
                TRACE("arith", tout << "Could not internalize " << mk_pp(atom, m) << "\n";);
                found_not_handled(atom);
                return true;
            }
            lp::bound* b = alloc(lp::bound, bv, v, r, k);
            m_bounds[v].push_back(b);
            updt_unassigned_bounds(v, +1);
            m_bounds_trail.push_back(v);
            m_bool_var2bound.insert(bv, b);
            TRACE("arith", tout << "Internalized " << mk_pp(atom, m) << "\n";);
            mk_bound_axioms(*b);
            return true;
        }

        bool internalize_atom_lazy(app * atom, bool gate_ctx) {
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
            updt_unassigned_bounds(v, +1);
            m_bounds_trail.push_back(v);
            m_bool_var2bound.insert(bv, b);
            TRACE("arith", tout << "Internalized " << mk_pp(atom, m) << "\n";);
            if (!is_unit_var(st) && m_bounds[v].size() == 1) {
                m_delayed_defs.push_back(delayed_def(st.vars(), st.coeffs(), st.coeff(), v)); 
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
            ++m_stats.m_assert_diseq;
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
                lean::var_index vi = m_theory_var2var_index[m_var_trail[i]];
                if (m_solver->is_term(vi)) {
                    unsigned ti = m_solver->adjust_term_index(vi);
                    m_term_index2theory_var[ti] = UINT_MAX;
                }
                else if (vi < m_var_index2theory_var.size()) {
                    m_var_index2theory_var[vi] = UINT_MAX;
                }
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
            m_new_bounds.reset();
            TRACE("arith", tout << m_scopes.size() << "\n";);
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
            //            literal eqz        = th.mk_eq(q, zero, false);
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
            m_num_conflicts = 0;
        }

        bool can_get_value(theory_var v) const {
            return 
                (v != null_theory_var) &&
                (v < static_cast<theory_var>(m_theory_var2var_index.size())) && 
                (UINT_MAX != m_theory_var2var_index[v]) && 
                (m_solver->is_term(m_theory_var2var_index[v]) || m_variable_values.count(m_theory_var2var_index[v]) > 0);
        }

        rational get_value(theory_var v) const {
            if (!can_get_value(v)) return rational::zero();
            lean::var_index vi = m_theory_var2var_index[v];
            if (m_variable_values.count(vi) > 0) {
                return m_variable_values[vi];
            }
            if (m_solver->is_term(vi)) {
                const lean::lar_term& term = m_solver->get_term(vi);
                rational result = term.m_v;
                for (unsigned i = 0; i < term.m_coeffs.size(); ++i) {
                    result += m_variable_values[term.m_coeffs[i].second] * term.m_coeffs[i].first;
                }
                m_variable_values[vi] = result;
                return result;
            }
            UNREACHABLE();
            return m_variable_values[vi];        
        }

        void init_variable_values() {
            if (m_solver.get() && th.get_num_vars() > 0) {
                m_solver->get_model(m_variable_values);
            }
        }

        void reset_variable_values() {
            m_variable_values.clear();
        }

        bool assume_eqs() {        
            svector<lean::var_index> vars;
            theory_var sz = static_cast<theory_var>(th.get_num_vars());
            for (theory_var v = 0; v < sz; ++v) {
                if (th.is_relevant_and_shared(get_enode(v))) { 
                    vars.push_back(m_theory_var2var_index[v]);
                }
            }
            if (vars.empty()) {
                return false;
            }
            TRACE("arith", 
                  for (theory_var v = 0; v < sz; ++v) {
                      if (th.is_relevant_and_shared(get_enode(v))) { 
                          tout << "v" << v << " " << m_theory_var2var_index[v] << " ";
                      }
                  }
                  tout << "\n";
                  );
            m_solver->random_update(vars.size(), vars.c_ptr());
            init_variable_values();
            m_model_eqs.reset();
            TRACE("arith", display(tout););
            
            unsigned old_sz = m_assume_eq_candidates.size();
            bool result = false;
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
                    TRACE("arith", tout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << "\n";
                          tout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << "\n";
                          tout << "v" << v << " = " << "v" << other << "\n";);
                    m_assume_eq_candidates.push_back(std::make_pair(v, other));
                    result = true;
                }
            }
            
            if (result) {
                ctx().push_trail(restore_size_trail<context, std::pair<theory_var, theory_var>, false>(m_assume_eq_candidates, old_sz));
            }

            return delayed_assume_eqs();
        }

        bool delayed_assume_eqs() {
            if (m_assume_eq_head == m_assume_eq_candidates.size())
                return false;
            
            ctx().push_trail(value_trail<context, unsigned>(m_assume_eq_head));
            while (m_assume_eq_head < m_assume_eq_candidates.size()) {
                std::pair<theory_var, theory_var> const & p = m_assume_eq_candidates[m_assume_eq_head];
                theory_var v1 = p.first;
                theory_var v2 = p.second;
                enode* n1 = get_enode(v1);
                enode* n2 = get_enode(v2);
                m_assume_eq_head++;
                CTRACE("arith", 
                       get_value(v1) == get_value(v2) && n1->get_root() != n2->get_root(),
                       tout << "assuming eq: v" << v1 << " = v" << v2 << "\n";);
                if (get_value(v1) == get_value(v2) &&  n1->get_root() != n2->get_root() && th.assume_eq(n1, n2)) {
                    return true;
                }
            }
            return false;
        }

        bool has_delayed_constraints() const {
            return !(m_asserted_atoms.empty() && m_delayed_terms.empty() && m_delayed_equalities.empty());
        }

        final_check_status final_check_eh() {
            lbool is_sat = l_true;
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
                is_sat = make_feasible();
            }
            else if (m_solver->get_status() != lean::lp_status::OPTIMAL) {
                is_sat = make_feasible();
            }
            switch (is_sat) {
            case l_true:
                init_variable_values();
                if (delayed_assume_eqs()) {
                    return FC_CONTINUE;
                }
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
#if 0
            if (ctx().at_base_level() && has_delayed_constraints()) {
                // we could add the delayed constraints here directly to the tableau instead of using bounds variables.
            }
#endif
            return m_asserted_atoms.size() > m_asserted_qhead;
        }

        void propagate() {
            flush_bound_axioms();
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
            lbool lbl = make_feasible();
            
            switch(lbl) {
            case l_false:
                TRACE("arith", tout << "propagation conflict\n";);
                set_conflict();
                break;
            case l_true:
                propagate_bounds_with_lp_solver();
                break;
            case l_undef:
                break;
            }
            
        }

        void propagate_bounds_with_lp_solver() {
            if (BP_NONE == propagation_mode()) {
                return;
            }
            std::vector<lean::bound_evidence> bound_evidences;
            int num_of_p = m_solver->settings().st().m_num_of_implied_bounds;
            m_solver->propagate_bounds_for_touched_rows(bound_evidences);
            int new_num_of_p = m_solver->settings().st().m_num_of_implied_bounds;
            CTRACE("arith", new_num_of_p > num_of_p, tout << "found " << new_num_of_p << " implied bounds\n";);
            if (m_solver->get_status() == lean::lp_status::INFEASIBLE) {
                set_conflict();
            }
            else {
                for (size_t i = 0; !ctx().inconsistent() && i < bound_evidences.size(); ++i) {
                    propagate_lp_solver_bound(bound_evidences[i]);
                }
            }
        }

        void propagate_lp_solver_bound(lean::bound_evidence const& be) {
            theory_var v;
            lean::var_index vi = be.m_j;
            if (m_solver->is_term(vi)) {
                v = m_term_index2theory_var.get(m_solver->adjust_term_index(vi), null_theory_var);
            }
            else {
                v = m_var_index2theory_var.get(vi, null_theory_var);
            }

            if (v == null_theory_var) return;
            TRACE("arith", tout << "v" << v << " " << be.m_kind << " " << be.m_bound << "\n";);

            if (m_unassigned_bounds[v] == 0 || m_bounds.size() <= static_cast<unsigned>(v)) {
                return;
            }
            lp_bounds const& bounds = m_bounds[v];
            for (unsigned i = 0; i < bounds.size(); ++i) {
                lp::bound* b = bounds[i];
                if (ctx().get_assignment(b->get_bv()) != l_undef) {
                    continue;
                }
                literal lit = is_bound_implied(be.m_kind, be.m_bound, *b);
                if (lit == null_literal) {
                    continue;
                }
                m_core.reset();
                m_eqs.reset();
                vector<parameter> params;
                for (size_t j = 0; j < be.m_evidence.size(); ++j) {
                    // be.m_evidence[j].first; // TBD coefficient. used for Farkas justification.
                    set_evidence(be.m_evidence[j].second);
                }
                updt_unassigned_bounds(v, -1);
                TRACE("arith",
                      ctx().display_literal_verbose(tout, lit);
                      ctx().display_literals_verbose(tout, m_core););
                
                ++m_stats.m_bound_propagations1;
                ctx().assign(
                    lit, ctx().mk_justification(
                        ext_theory_propagation_justification(
                            get_id(), ctx().get_region(), m_core.size(), m_core.c_ptr(), 
                            m_eqs.size(), m_eqs.c_ptr(), lit, params.size(), params.c_ptr())));
            }     
        }

        literal is_bound_implied(lean::lconstraint_kind k, rational const& value, lp::bound const& b) {
            if ((k == lean::LE || k == lean::LT) && b.get_bound_kind() == lp::upper_t && value <= b.get_value()) {
                // v <= value <= b.get_value() => v <= b.get_value() 
                return literal(b.get_bv(), false);
            }
            if ((k == lean::GE || k == lean::GT) && b.get_bound_kind() == lp::lower_t && b.get_value() <= value) {
                // b.get_value() <= value <= v => b.get_value() <= v 
                return literal(b.get_bv(), false);
            }
            if (k == lean::LE && b.get_bound_kind() == lp::lower_t && value < b.get_value()) {
                // v <= value < b.get_value() => v < b.get_value()
                return literal(b.get_bv(), true);
            }
            if (k == lean::LT && b.get_bound_kind() == lp::lower_t && value <= b.get_value()) {
                // v < value <= b.get_value() => v < b.get_value()
                return literal(b.get_bv(), true);
            }
            if (k == lean::GE && b.get_bound_kind() == lp::upper_t && b.get_value() < value) {
                // b.get_value() < value <= v => b.get_value() < v
                return literal(b.get_bv(), true);
            }
            if (k == lean::GT && b.get_bound_kind() == lp::upper_t && b.get_value() <= value) {
                // b.get_value() <= value < v => b.get_value() < v
                return literal(b.get_bv(), true);
            }

            return null_literal;
        }

        void mk_bound_axioms(lp::bound& b) {
            // b.display(std::cout); std::cout << "\n";
            if (!ctx().is_searching()) {
                //
                // NB. We make an assumption that user push calls propagation 
                // before internal scopes are pushed. This flushes all newly 
                // asserted atoms into the right context.
                //
                m_new_bounds.push_back(&b);
                return;
            }
            theory_var v = b.get_var();
            lp::bound_kind kind1 = b.get_bound_kind();
            rational const& k1 = b.get_value();
            lp_bounds & bounds = m_bounds[v];

            lp::bound* end = 0;
            lp::bound* lo_inf = end, *lo_sup = end;
            lp::bound* hi_inf = end, *hi_sup = end;
            
            for (unsigned i = 0; i < bounds.size(); ++i) {
                lp::bound& other = *bounds[i];
                if (&other == &b) continue;
                if (b.get_bv() == other.get_bv()) continue;
                lp::bound_kind kind2 = other.get_bound_kind();
                rational const& k2 = other.get_value();
                if (k1 == k2 && kind1 == kind2) {
                    // the bounds are equivalent.
                    continue;
                }

                SASSERT(k1 != k2 || kind1 != kind2);
                if (kind2 == lp::lower_t) {
                    if (k2 < k1) {
                        if (lo_inf == end || k2 > lo_inf->get_value()) {
                            lo_inf = &other;
                        }
                    }
                    else if (lo_sup == end || k2 < lo_sup->get_value()) {
                        lo_sup = &other;
                    }
                }
                else if (k2 < k1) {
                    if (hi_inf == end || k2 > hi_inf->get_value()) {
                        hi_inf = &other;
                    }
                }
                else if (hi_sup == end || k2 < hi_sup->get_value()) {
                    hi_sup = &other;
                }
            }        
            if (lo_inf != end) mk_bound_axiom(b, *lo_inf);
            if (lo_sup != end) mk_bound_axiom(b, *lo_sup);
            if (hi_inf != end) mk_bound_axiom(b, *hi_inf);
            if (hi_sup != end) mk_bound_axiom(b, *hi_sup);
        }


        void mk_bound_axiom(lp::bound& b1, lp::bound& b2) {
            theory_var v = b1.get_var();
            literal   l1(b1.get_bv());
            literal   l2(b2.get_bv());
            rational const& k1 = b1.get_value();
            rational const& k2 = b2.get_value();
            lp::bound_kind kind1 = b1.get_bound_kind();
            lp::bound_kind kind2 = b2.get_bound_kind();
            bool v_is_int = is_int(v);
            SASSERT(v == b2.get_var());
            if (k1 == k2 && kind1 == kind2) return;
            SASSERT(k1 != k2 || kind1 != kind2);
            parameter coeffs[3] = { parameter(symbol("farkas")), 
                                    parameter(rational(1)), parameter(rational(1)) };
            
            if (kind1 == lp::lower_t) {
                if (kind2 == lp::lower_t) {
                    if (k2 <= k1) {
                        mk_clause(~l1, l2, 3, coeffs);
                    }
                    else {
                        mk_clause(l1, ~l2, 3, coeffs);
                    }
                }
                else if (k1 <= k2) {
                    // k1 <= k2, k1 <= x or x <= k2
                    mk_clause(l1, l2, 3, coeffs);
                }
                else {
                    // k1 > hi_inf, k1 <= x => ~(x <= hi_inf)
                    mk_clause(~l1, ~l2, 3, coeffs);
                    if (v_is_int && k1 == k2 + rational(1)) {
                        // k1 <= x or x <= k1-1
                        mk_clause(l1, l2, 3, coeffs);
                    }
                }
            }
            else if (kind2 == lp::lower_t) {
                if (k1 >= k2) {
                    // k1 >= lo_inf, k1 >= x or lo_inf <= x
                    mk_clause(l1, l2, 3, coeffs);
                }
                else {
                    // k1 < k2, k2 <= x => ~(x <= k1)
                    mk_clause(~l1, ~l2, 3, coeffs); 
                    if (v_is_int && k1 == k2 - rational(1)) {
                        // x <= k1 or k1+l <= x
                        mk_clause(l1, l2, 3, coeffs);
                    }
                    
                }
            }
            else {
                // kind1 == A_UPPER, kind2 == A_UPPER
                if (k1 >= k2) {
                    // k1 >= k2, x <= k2 => x <= k1
                    mk_clause(l1, ~l2, 3, coeffs);
                }
                else {
                    // k1 <= hi_sup , x <= k1 =>  x <= hi_sup
                    mk_clause(~l1, l2, 3, coeffs);
                }
            }        
        }

        typedef lp_bounds::iterator iterator;

        void flush_bound_axioms() {
            CTRACE("arith", !m_new_bounds.empty(), tout << "flush bound axioms\n";);

            while (!m_new_bounds.empty()) {
                lp_bounds atoms;            
                atoms.push_back(m_new_bounds.back());
                m_new_bounds.pop_back();
                theory_var v = atoms.back()->get_var();
                for (unsigned i = 0; i < m_new_bounds.size(); ++i) {
                    if (m_new_bounds[i]->get_var() == v) {
                        atoms.push_back(m_new_bounds[i]);
                        m_new_bounds[i] = m_new_bounds.back();
                        m_new_bounds.pop_back();
                        --i;
                    }
                }            
                CTRACE("arith_verbose", !atoms.empty(),  
                       for (unsigned i = 0; i < atoms.size(); ++i) {
                           atoms[i]->display(tout); tout << "\n";
                       });
                lp_bounds occs(m_bounds[v]);
                
                std::sort(atoms.begin(), atoms.end(), compare_bounds());
                std::sort(occs.begin(), occs.end(), compare_bounds());
                
                iterator begin1 = occs.begin();
                iterator begin2 = occs.begin();
                iterator end = occs.end();
                begin1 = first(lp::lower_t, begin1, end);
                begin2 = first(lp::upper_t, begin2, end);
                
                iterator lo_inf = begin1, lo_sup = begin1;
                iterator hi_inf = begin2, hi_sup = begin2;
                iterator lo_inf1 = begin1, lo_sup1 = begin1;
                iterator hi_inf1 = begin2, hi_sup1 = begin2;
                bool flo_inf, fhi_inf, flo_sup, fhi_sup;
                ptr_addr_hashtable<lp::bound> visited;
                for (unsigned i = 0; i < atoms.size(); ++i) {
                    lp::bound* a1 = atoms[i];
                    lo_inf1 = next_inf(a1, lp::lower_t, lo_inf, end, flo_inf);
                    hi_inf1 = next_inf(a1, lp::upper_t, hi_inf, end, fhi_inf);
                    lo_sup1 = next_sup(a1, lp::lower_t, lo_sup, end, flo_sup);
                    hi_sup1 = next_sup(a1, lp::upper_t, hi_sup, end, fhi_sup);
                    if (lo_inf1 != end) lo_inf = lo_inf1; 
                    if (lo_sup1 != end) lo_sup = lo_sup1; 
                    if (hi_inf1 != end) hi_inf = hi_inf1; 
                    if (hi_sup1 != end) hi_sup = hi_sup1; 
                    if (!flo_inf) lo_inf = end;
                    if (!fhi_inf) hi_inf = end;
                    if (!flo_sup) lo_sup = end;
                    if (!fhi_sup) hi_sup = end;
                    visited.insert(a1);
                    if (lo_inf1 != end && lo_inf != end && !visited.contains(*lo_inf)) mk_bound_axiom(*a1, **lo_inf);
                    if (lo_sup1 != end && lo_sup != end && !visited.contains(*lo_sup)) mk_bound_axiom(*a1, **lo_sup);
                    if (hi_inf1 != end && hi_inf != end && !visited.contains(*hi_inf)) mk_bound_axiom(*a1, **hi_inf);
                    if (hi_sup1 != end && hi_sup != end && !visited.contains(*hi_sup)) mk_bound_axiom(*a1, **hi_sup);
                }                            
            }
        }

        struct compare_bounds {
            bool operator()(lp::bound* a1, lp::bound* a2) const { return a1->get_value() < a2->get_value(); }
        };


        lp_bounds::iterator first(
            lp::bound_kind kind, 
            iterator it, 
            iterator end) {
            for (; it != end; ++it) {
                lp::bound* a = *it;
                if (a->get_bound_kind() == kind) return it;
            }
            return end;
        }

        lp_bounds::iterator next_inf(
            lp::bound* a1, 
            lp::bound_kind kind, 
            iterator it, 
            iterator end,
            bool& found_compatible) {
            rational const & k1(a1->get_value());
            iterator result = end;
            found_compatible = false;
            for (; it != end; ++it) {
                lp::bound * a2 = *it;            
                if (a1 == a2) continue;
                if (a2->get_bound_kind() != kind) continue;
                rational const & k2(a2->get_value());
                found_compatible = true;
                if (k2 <= k1) {
                    result = it;
                }
                else {
                    break;
                }
            }
            return result;
        }

        lp_bounds::iterator next_sup(
            lp::bound* a1, 
            lp::bound_kind kind, 
            iterator it, 
            iterator end,
            bool& found_compatible) {
            rational const & k1(a1->get_value());
            found_compatible = false;
            for (; it != end; ++it) {
                lp::bound * a2 = *it;            
                if (a1 == a2) continue;
                if (a2->get_bound_kind() != kind) continue;
                rational const & k2(a2->get_value());
                found_compatible = true;
                if (k1 < k2) {
                    return it;
                }
            }
            return end;
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
            lp_bounds const& bounds = m_bounds[v];
            SASSERT(!bounds.empty());
            if (bounds.size() == 1) return;
            if (m_unassigned_bounds[v] == 0) return;

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
            updt_unassigned_bounds(v, -1);
            ++m_stats.m_bound_propagations2;
            parameter coeffs[3] = { parameter(symbol("farkas")), parameter(rational(1)), parameter(rational(1)) };
            ctx().assign(
                lit2, ctx().mk_justification(
                    theory_propagation_justification(
                        get_id(), ctx().get_region(), 1, &lit1, lit2, 3, coeffs)));
            ++m_stats.m_bounds_propagations;
        }

#if 0
        //
        // propagate bounds to compound terms
        // The idea is that if bounds on all variables in an inequality ax + by + cz >= k
        // have been assigned we may know the truth value of the inequality by using simple
        // bounds propagation.
        // 
        void propagate_bound_compound(bool_var bv, bool is_true, lp::bound& b) {
            lp::bound_kind k = b.get_bound_kind();
            theory_var v = b.get_var();
            inf_rational val = b.get_value(is_true);
            // TBD:
            // for (bound& tb: m_use_list[v])
            //     if (ctx().get_assignment(tb.get_bv()) != l_undef) continue;
            //     evaluate tb under current bounds
            //     to determine a glb or lub
            //     if glb >= tb.get_value()...
            //        apply propagation.
            // 
        }

        bool get_lub(bound const& b, inf_rational& lub) {
            return false;
        }

        bool get_glb(bound const& b, inf_rational& glb) {
            return false;
        }
#endif

        void assert_bound(bool_var bv, bool is_true, lp::bound& b) {
            if (m_solver->get_status() == lean::lp_status::INFEASIBLE) {
                return;
            }
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
            auto vi = get_var_index(b.get_var());
            auto ci = m_solver->add_var_bound(vi, k, b.get_value());
            add_ineq_constraint(ci, literal(bv, !is_true));

            propagate_eqs(vi, ci, k, b);
        }

        //
        // fixed equalities.
        // A fixed equality is inferred if there are two variables v1, v2 whose
        // upper and lower bounds coincide.
        // Then the equality v1 == v2 is propagated to the core.
        // 

        typedef std::pair<lean::constraint_index, rational> constraint_bound;
        vector<constraint_bound>        m_lower_terms;
        vector<constraint_bound>        m_upper_terms;
        typedef std::pair<rational, bool> value_sort_pair;
        typedef pair_hash<obj_hash<rational>, bool_hash> value_sort_pair_hash;
        typedef map<value_sort_pair, theory_var, value_sort_pair_hash, default_eq<value_sort_pair> > value2var;
        value2var               m_fixed_var_table;
        const lean::constraint_index null_index = static_cast<lean::constraint_index>(-1);

        void propagate_eqs(lean::var_index vi, lean::constraint_index ci, lean::lconstraint_kind k, lp::bound& b) {
            if (propagate_eqs()) {
                rational const& value = b.get_value();
                if (k == lean::GE) {
                    set_lower_bound(vi, ci, value);
                    if (has_upper_bound(vi, ci, value)) {
                        fixed_var_eh(b.get_var(), value);
                    }
                }
                else if (k == lean::LE) {
                    set_upper_bound(vi, ci, value);
                    if (has_lower_bound(vi, ci, value)) {
                        fixed_var_eh(b.get_var(), value);
                    }
                }
            }
        }

        bool propagate_eqs() const { return m_params.m_arith_propagate_eqs && m_num_conflicts < m_params.m_arith_propagation_threshold; }

        bound_prop_mode propagation_mode() const { return m_num_conflicts < m_params.m_arith_propagation_threshold ? m_params.m_arith_bound_prop : BP_NONE; }

        void set_upper_bound(lean::var_index vi, lean::constraint_index ci, rational const& v) { set_bound(vi, ci, v, false);  }

        void set_lower_bound(lean::var_index vi, lean::constraint_index ci, rational const& v) { set_bound(vi, ci, v, true);   }

        void set_bound(lean::var_index vi, lean::constraint_index ci, rational const& v, bool is_lower) {
            if (!m_solver->is_term(vi)) {
                // m_solver already tracks bounds on proper variables, but not on terms.
                return;
            }
            lean::var_index ti = m_solver->adjust_term_index(vi);
            auto& vec = is_lower ? m_lower_terms : m_upper_terms;
            if (vec.size() <= ti) {
                vec.resize(ti + 1, constraint_bound(null_index, rational()));
            }
            constraint_bound& b = vec[ti];
            if (b.first == null_index || (is_lower? b.second < v : b.second > v)) {
                ctx().push_trail(vector_value_trail<context, constraint_bound>(vec, ti));
                b.first = ci;
                b.second = v;
            }
        }

        bool has_upper_bound(lean::var_index vi, lean::constraint_index& ci, rational const& bound) { return has_bound(vi, ci, bound, false); }

        bool has_lower_bound(lean::var_index vi, lean::constraint_index& ci, rational const& bound) { return has_bound(vi, ci, bound, true); }
       
        bool has_bound(lean::var_index vi, lean::constraint_index& ci, rational const& bound, bool is_lower) {
            if (m_solver->is_term(vi)) {
                lean::var_index ti = m_solver->adjust_term_index(vi);
                auto& vec = is_lower ? m_lower_terms : m_upper_terms;
                if (vec.size() > ti) {
                    constraint_bound& b = vec[ti];
                    ci = b.first;
                    return ci != null_index && bound == b.second;
                }
                else {
                    return false;

                }
            }
            else {
                bool is_strict = false;
                rational b;
                if (is_lower) {
                    return m_solver->has_lower_bound(vi, ci, b, is_strict) && b == bound && !is_strict;
                }
                else {
                    return m_solver->has_upper_bound(vi, ci, b, is_strict) && b == bound && !is_strict;
                }
            }
        }


        bool is_equal(theory_var x, theory_var y) const { return get_enode(x)->get_root() == get_enode(y)->get_root(); }


        void fixed_var_eh(theory_var v1, rational const& bound) {
            theory_var v2;
            value_sort_pair key(bound, is_int(v1));
            if (m_fixed_var_table.find(key, v2)) {
                if (static_cast<unsigned>(v2) < th.get_num_vars() && !is_equal(v1, v2)) {
                    auto vi1 = get_var_index(v1);
                    auto vi2 = get_var_index(v2);
                    lean::constraint_index ci1, ci2, ci3, ci4;
                    if (has_lower_bound(vi2, ci3, bound) && has_upper_bound(vi2, ci4, bound)) {
                        VERIFY (has_lower_bound(vi1, ci1, bound));
                        VERIFY (has_upper_bound(vi1, ci2, bound));
                        ++m_stats.m_fixed_eqs;
                        TRACE("arith", tout << "fixing v" << v1 << " == v" << v2 << "\n";);
                        m_core.reset();
                        m_eqs.reset();
                        set_evidence(ci1);
                        set_evidence(ci2);
                        set_evidence(ci3);
                        set_evidence(ci4);
                        enode* x = get_enode(v1);
                        enode* y = get_enode(v2);
                        justification* js = 
                            ctx().mk_justification(
                                ext_theory_eq_propagation_justification(
                                    get_id(), ctx().get_region(), m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), x, y, 0, 0));
                        // parameters are TBD.
                        ctx().assign_eq(x, y, eq_justification(js));
                    }
                    else {
                        // bounds on v2 were changed.
                        m_fixed_var_table.insert(key, v1);
                    }
                }
            }
            else {
                m_fixed_var_table.insert(key, v1);
            }
        }

        lbool make_feasible() {
            //static unsigned m_count = 0;
            //std::cout << "check feasible " << m_count++ << "\n";
            reset_variable_values();
            TRACE("arith_verbose", display(tout););
            stopwatch sw;
            sw.start();
            lean::lp_status status = m_solver->solve();
            sw.stop();
            m_stats.m_num_iterations = m_solver->settings().st().m_total_iterations;
            m_stats.m_num_factorizations = m_solver->settings().st().m_num_factorizations;

            if (m_print_counter++ % 1000 == 0) {
                std::cout << status << " " << sw.get_seconds() << " " << m_stats.m_num_iterations << " " << m_print_counter << "\n";
            }
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

        std::vector<std::pair<rational, lean::constraint_index>> m_evidence;
        literal_vector      m_core;
        svector<enode_pair> m_eqs;

        void set_evidence(lean::constraint_index idx) {
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

        void set_conflict() {
            m_eqs.reset();
            m_core.reset();
            m_evidence.clear();
            m_solver->get_infeasibility_evidence(m_evidence);
            ++m_num_conflicts;
            ++m_stats.m_conflicts;
            TRACE("arith", display_evidence(tout, m_evidence); );
            for (auto const& ev : m_evidence) {
                if (!ev.first.is_zero()) { 
                    set_evidence(ev.second);
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
            m_unassigned_bounds.reset();
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

        void display_evidence(std::ostream& out, std::vector<std::pair<rational, lean::constraint_index>> const& evidence) {
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
                default:
                    SASSERT(false);  // it seems the control should not be here
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
            st.update("arith-factorizations", m_stats.m_num_factorizations);
            st.update("arith-plateau-iterations", m_stats.m_num_iterations_with_no_progress);
            st.update("arith-fixed-eqs", m_stats.m_fixed_eqs);
            st.update("arith-conflicts", m_stats.m_conflicts);
            st.update("arith-bound-propagations-lp", m_stats.m_bound_propagations1);
            st.update("arith-bound-propagations-cheap", m_stats.m_bound_propagations2);
            st.update("arith-diseq", m_stats.m_assert_diseq);
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
