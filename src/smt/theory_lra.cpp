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
#include "util/lp/lp_solver.h"
#include "util/lp/lp_primal_simplex.h"
#include "util/lp/lp_dual_simplex.h"
#include "util/lp/indexed_value.h"
#include "util/lp/lar_solver.h"
#include "util/nat_set.h"
#include "util/optional.h"
#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "smt/theory_lra.h"
#include "smt/proto_model/numeral_factory.h"
#include "smt/smt_model_generator.h"
#include "smt/arith_eq_adapter.h"

namespace lp {
    enum bound_kind { lower_t, upper_t };

    //typedef std::pair<rational, rational> inf_numeral;
    typedef rational inf_numeral;

    std::ostream& operator<<(std::ostream& out, bound_kind const& k) {
        switch (k) {
        case lower_t: return out << "<=";
        case upper_t: return out << ">=";
        }
        return out;
    }

    class bound { 
    protected:
        smt::theory_var  m_var;
        inf_numeral      m_value; // tbd: inf_numeral
        bound_kind       m_bound_kind;
        bool             m_true;

    public:
        bound(smt::theory_var v, inf_numeral const & val, bound_kind k):
            m_var(v),
            m_value(val),
            m_bound_kind(k), 
            m_true(false) {
        }
        virtual ~bound() {}
        smt::theory_var get_var() const { return m_var; }
        bound_kind get_bound_kind() const { return m_true?m_bound_kind:static_cast<bound_kind>(1-m_bound_kind); }
        bool get_phase() const { return m_true; }
        void set_phase(bool t) { m_true = t; }
        inf_numeral const & get_value() const { return m_value; } // tbd: adjust with infinitesimals if negated.
        virtual std::ostream& display(std::ostream& out) const {
            return out << "v" << get_var() << "  " << get_bound_kind() << " " << get_value();
        }
    };

    std::ostream& operator<<(std::ostream& out, bound const& b) {
        return b.display(out);
    }

    struct stats {
        unsigned m_assert_lower;
        unsigned m_assert_upper;
        stats() { reset(); }
        void reset() {
            memset(this, 0, sizeof(*this));
        }
    };

    typedef optional<inf_numeral> opt_inf_numeral;

    struct replay_bound {
        smt::theory_var   m_v;
        opt_inf_numeral   m_bound;
        bound_kind        m_bound_kind;
        
        replay_bound(smt::theory_var v, opt_inf_numeral const& n, bound_kind k):
            m_v(v), m_bound(n), m_bound_kind(k)
        {}
    };


}

namespace smt {


    class theory_lra::imp {        

        struct scope {
            unsigned m_bounds_lim;
            unsigned m_asserted_qhead;            
            unsigned m_replay_lim;
            unsigned m_delayed_atoms_lim;
            unsigned m_internalized_terms_lim;
            unsigned m_delayed_equalities_lim;
            expr*    m_not_handled;
        };

        struct delayed_atom {
            unsigned m_bv;
            bool     m_is_true;
            delayed_atom(unsigned b, bool t): m_bv(b), m_is_true(t) {}
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
        internalize_state& push_internalize() {
            if (m_internalize_head == m_internalize_states.size()) {
                m_internalize_states.push_back(alloc(internalize_state, m));
            }
            internalize_state& st = *m_internalize_states[m_internalize_head++];
            st.reset();
            return st;
        }
        void pop_internalize() {
            --m_internalize_head;
        }

        class scoped_internalize_state {
            imp& m_imp;
            internalize_state& m_st;
        public:
            scoped_internalize_state(imp& i): m_imp(i), m_st(i.push_internalize()) {}
            ~scoped_internalize_state() { m_imp.pop_internalize(); }
            expr_ref_vector&     terms() { return m_st.m_terms; }                     
            vector<rational>&    coeffs() { return m_st.m_coeffs; }
            svector<theory_var>& vars() { return m_st.m_vars; }
            rational&            coeff() { return m_st.m_coeff; }
            ptr_vector<expr>&    terms_to_internalize() { return m_st.m_terms_to_internalize; }            
        };

        

        svector<lean::var_index> m_theory_var2var_index;          // translate from theory variables to lar vars
        buffer<std::pair<rational, lean::var_index>>  m_left_side; // constraint left side
        mutable std::unordered_map<lean::var_index, rational> m_variable_values; // current model

        enum constraint_source {
            inequality_source,
            equality_source,
            definition_source,
            null_source
        };
        svector<constraint_source>                    m_constraint_sources;
        svector<literal>                              m_inequalities;    // asserted rows corresponding to literals.
        svector<enode_pair>                           m_equalities;      // asserted rows corresponding to equalities.
        svector<theory_var>                           m_definitions;     // asserted rows corresponding to definitions

        bool                   m_delay_atoms;    // configuration
        svector<delayed_atom>  m_delayed_atoms;        
        app_ref_vector         m_internalized_terms;        
        svector<std::pair<theory_var, theory_var>> m_delayed_equalities;
        expr*                  m_not_handled;

        // attributes for incremental version:
        u_map<lp::bound*>      m_bool_var2bound;
        ptr_vector<lp::bound>  m_bounds;
        ptr_vector<lp::bound>  m_asserted_bounds;
        unsigned               m_asserted_qhead;
        vector<lp::replay_bound>   m_replay_bounds;
        vector<lp::opt_inf_numeral> m_lower, m_upper;


        svector<scope>         m_scopes;
        lp::stats              m_stats;
        

        arith_factory*         m_factory;
        

        scoped_ptr<lean::lar_solver> m_solver;

        context& ctx() { return th.get_context(); }

        void found_not_handled(expr* n) {
            m_not_handled = n;
            TRACE("arith", tout << "Unhandled: " << mk_pp(n, m) << "\n";);
        }

        bool is_numeral(expr* term, rational& r) {
            if (a.is_uminus(term, term) && is_numeral(term, r)) {
                r.neg();
                return true;
            }
            return a.is_numeral(term, r);
        }

        void linearize(expr* term, scoped_internalize_state& st) { 
            expr_ref_vector & terms = st.terms();
            svector<theory_var>& vars = st.vars();
            vector<rational>& coeffs = st.coeffs();
            rational& coeff = st.coeff();
            terms.push_back(term);
            coeffs.push_back(rational(1));

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
                        terms.push_back(to_app(n)->get_arg(i));
                        coeffs.push_back(coeffs[index]);
                    }
                    terms[index] = terms.back();
                    coeffs[index] = coeffs.back();
                    terms.pop_back();
                    coeffs.pop_back();
                }
                else if (a.is_sub(n)) {
                    unsigned sz = to_app(n)->get_num_args();
                    terms[index] = to_app(n)->get_arg(0);                    
                    for (unsigned i = 1; i < sz; ++i) {
                        terms.push_back(to_app(n)->get_arg(i));
                        coeffs.push_back(-coeffs[index]);
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
                    coeff += r;
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
                return ctx().get_enode(n);
            }
            else {
                return ctx().mk_enode(n, !reflect(n), false, enable_cgc_for(n));       
            }
        }

        bool enable_cgc_for(app * n) const {
            // Congruence closure is not enabled for (+ ...) and (* ...) applications.
            return !(n->get_family_id() == th.get_id() && (n->get_decl_kind() == OP_ADD || n->get_decl_kind() == OP_MUL));
        }

        bool reflect(app* n) const {
            return true;
        }

        theory_var mk_var(expr* n, bool internalize = true) {
            if (!ctx().e_internalized(n)) {
                ctx().internalize(n, false);                
            }
            enode* e = ctx().get_enode(n);
            theory_var v;
            if (!th.is_attached_to_var(e)) {
                v = th.mk_var(e);                        
                ctx().attach_th_var(e, &th, v);
            }
            else {
                v = e->get_th_var(th.get_id());                
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
                s << v;
                result = m_solver->add_var(s.str());
                m_theory_var2var_index.setx(v, result, UINT_MAX);
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
                TRACE("arith", tout << var << ":" << coeff << "\n";);
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
        }
        
        void add_ineq_constraint(lean::constraint_index index, literal lit) {
            m_constraint_sources.setx(index, inequality_source, null_source);
            m_inequalities.setx(index, lit, null_literal);
        }
        
        void add_def_constraint(lean::constraint_index index, theory_var v) {
            m_constraint_sources.setx(index, definition_source, null_source);
            m_definitions.setx(index, v, null_theory_var);
        }
        
        void internalize_eq(theory_var v1, theory_var v2) {
            enode* n1 = th.get_enode(v1);
            enode* n2 = th.get_enode(v2);
            scoped_internalize_state st(*this);
            st.vars().push_back(v1);
            st.vars().push_back(v2);
            st.coeffs().push_back(rational::one());
            st.coeffs().push_back(rational::minus_one());
            init_left_side(st);
            add_eq_constraint(m_solver->add_constraint(m_left_side, lean::EQ, rational::zero()), n1, n2);
        }

        void internalize_ineq(expr* atom, bool_var bv, bool is_true) {
            TRACE("arith", tout << mk_pp(atom, m) << " " << is_true << "\n";);
            expr* n1, *n2;
            rational right_side;
            lean::lconstraint_kind k = lean::EQ;
            if (a.is_le(atom, n1, n2) && a.is_numeral(n2, right_side)) {
                k = is_true ? lean::LE : lean::GT;
            }
            else if (a.is_ge(atom, n1, n2) && a.is_numeral(n2, right_side)) {
                k = is_true ? lean::GE : lean::LT;
            }
            else {
                UNREACHABLE();
            }
            scoped_internalize_state st(*this);
            linearize(n1, st);
            init_left_side(st);
            right_side -= st.coeff();

            SASSERT(m_left_side.size() > 0);
            if (m_left_side.size() > 0) {
                add_ineq_constraint(m_solver->add_constraint(m_left_side, k, right_side), literal(bv, !is_true));
            }
        }


        void del_bounds(unsigned old_size) {
            for (unsigned i = m_bounds.size(); i > old_size; ) {
                --i;
                dealloc(m_bounds[i]);
            }
            m_bounds.shrink(old_size);
        }
        

        theory_var internalize_def(app* term) {
            scoped_internalize_state st(*this);
            theory_var v = internalize_term_core(term, st);
            init_left_side(st);
            add_def_constraint(m_solver->add_constraint(m_left_side, lean::EQ, -st.coeff()), v);
            return v;
        }
        
        theory_var internalize_term_core(app* term, scoped_internalize_state& st) {
            linearize(term, st);
            if (st.vars().size() == 1 && st.coeff().is_zero() && st.coeffs()[0].is_one()) {
                return st.vars()[0];
            }
            theory_var v = mk_var(term);
            SASSERT(null_theory_var != v);
            st.vars().push_back(v);
            st.coeffs().push_back(rational::minus_one());
            return v;
        }


    public:
        imp(theory_lra& th, ast_manager& m, theory_arith_params& p): 
            th(th), m(m), m_params(p), a(m), 
            m_arith_eq_adapter(th, p, a),
            m_internalize_head(0),
            m_asserted_qhead(0), 
            m_delay_atoms(true), 
            m_internalized_terms(m),
            m_not_handled(0) {
            m_solver = alloc(lean::lar_solver); 
        }
        
        ~imp() {
            del_bounds(0);
            std::for_each(m_internalize_states.begin(), m_internalize_states.end(), delete_proc<internalize_state>());
        }
        
        bool internalize_atom(app * atom, bool gate_ctx) {
            bool_var bv = ctx().mk_bool_var(atom);
            ctx().set_var_theory(bv, th.get_id());
            if (m_delay_atoms) {
                return true;
            }
            expr* n1, *n2;
            rational r;
            lp::bound_kind k;
            theory_var v = null_theory_var;
            if (a.is_le(atom, n1, n2) && a.is_numeral(n2, r) && is_app(n1)) {
                v = internalize_def(to_app(n1));
                k = lp::upper_t;
            }
            else if (a.is_ge(atom, n1, n2) && a.is_numeral(n2, r) && is_app(n1)) {
                v = internalize_def(to_app(n1));
                k = lp::lower_t;
            }    
            else {
                TRACE("arith", tout << "Could not internalize " << mk_pp(atom, m) << "\n";);
                return false;
            }
            lp::inf_numeral _r(r);
            lp::bound* b = alloc(lp::bound, v, _r, k);
            m_bounds.push_back(b);
            m_bool_var2bound.insert(bv, b);
            TRACE("arith", tout << "Internalized " << mk_pp(atom, m) << " " << b << "\n";);
            return true;
        }
        
        bool internalize_term(app * term) {
            if (m_delay_atoms) {
                scoped_internalize_state st(*this);
                internalize_term_core(term, st);  // ensure that a theory_var was created.
                m_internalized_terms.push_back(term);                
            }
            else {
                internalize_def(term);
            }
            return true;
        }
        
        void internalize_eq_eh(app * atom, bool_var v) {
            expr* lhs, *rhs;
            VERIFY(m.is_eq(atom, lhs, rhs));
            enode * n1 = ctx().get_enode(lhs);
            enode * n2 = ctx().get_enode(rhs);
            // The expression atom may be a theory axiom. In this case, it may not be in simplified form.
            // So, an atom such as (= a a) may occur. The procedure mk_axioms, expects n1 != n2. 
            // So, we should check it. It doesn't make sense to create an axiom for (= a a) in the arith_eq_adapter.
            if (n1->get_th_var(th.get_id()) != null_theory_var &&
                n2->get_th_var(th.get_id()) != null_theory_var &&
                n1 != n2) {
                TRACE("arith", tout << mk_pp(atom, m) << "\n";);
                m_arith_eq_adapter.mk_axioms(n1, n2);
            }
        }

        void assign_eh(bool_var v, bool is_true) {
            if (m_delay_atoms) {
                m_delayed_atoms.push_back(delayed_atom(v, is_true));
            }
            else {
                lp::bound* b = m_bool_var2bound[v];
                SASSERT(b);
                b->set_phase(is_true);
                m_asserted_bounds.push_back(b);
            }
        }

        void new_eq_eh(theory_var v1, theory_var v2) {
            if (m_delay_atoms) {
                m_delayed_equalities.push_back(std::make_pair(v1, v2));
            }
            else {
                m_arith_eq_adapter.new_eq_eh(v1, v2);
                // or internalize_eq(v1, v2);
            }
        }

        bool use_diseqs() const {
            return false;
        }

        void new_diseq_eh(theory_var v1, theory_var v2) {
            m_arith_eq_adapter.new_diseq_eh(v1, v2);
        }

        void push_scope_eh() {
            m_scopes.push_back(scope());
            scope& s = m_scopes.back();
            s.m_bounds_lim = m_bounds.size();
            s.m_asserted_qhead = m_asserted_qhead;
            s.m_replay_lim = m_replay_bounds.size();
            s.m_delayed_atoms_lim = m_delayed_atoms.size();
            s.m_internalized_terms_lim = m_internalized_terms.size();
            s.m_delayed_equalities_lim = m_delayed_equalities.size();
            s.m_not_handled = m_not_handled;
        }

        void pop_scope_eh(unsigned num_scopes) {
            if (num_scopes > 0) {
                unsigned old_size = m_scopes.size() - num_scopes;
                del_bounds(m_scopes[old_size].m_bounds_lim);
                m_delayed_atoms.shrink(m_scopes[old_size].m_delayed_atoms_lim);
                m_internalized_terms.shrink(m_scopes[old_size].m_internalized_terms_lim);
                m_delayed_equalities.shrink(m_scopes[old_size].m_delayed_equalities_lim);
                m_asserted_qhead = m_scopes[old_size].m_asserted_qhead;
                m_not_handled = m_scopes[old_size].m_not_handled;
                unsigned sz = m_scopes[old_size].m_replay_lim;
                for (unsigned i = m_replay_bounds.size(); i > sz; ) {
                    --i;
                    lp::replay_bound const& r = m_replay_bounds[i];
                    switch (r.m_bound_kind) {
                    case lp::lower_t:
                        m_lower[r.m_v] = r.m_bound;
                        // TBD: m_solver->unset_low_bound(r.m_v);
                        if (r.m_bound) {
                            // TBD: m_solver->set_low_bound(r.m_v, *r.m_bound);
                        }
                        break;
                    case lp::upper_t:
                        m_upper[r.m_v] = r.m_bound;
                        // TBD: m_solver->unset_upper_bound(r.m_v);
                        if (r.m_bound) {
                            // TBD: m_solver->set_upper_bound(r.m_v, *r.m_bound);
                        }
                        break;
                    }
                }
                m_replay_bounds.shrink(sz);
                m_scopes.resize(old_size);
            }
        }

        void restart_eh() {
            m_arith_eq_adapter.restart_eh();
        }

        void relevant_eh(app* e) {

        }

        void init_search_eh() {
            m_arith_eq_adapter.init_search_eh();
        }

        final_check_status final_check_eh() {
            if (m_delayed_atoms.empty()) {
                return FC_DONE;
            }
            m_solver = alloc(lean::lar_solver); 
            for (unsigned i = 0; i < m_delayed_atoms.size(); ++i) {
                bool_var bv = m_delayed_atoms[i].m_bv;
                expr* atom = ctx().bool_var2expr(bv);
                internalize_ineq(atom, bv, m_delayed_atoms[i].m_is_true);
            }
            for (unsigned i = 0; i < m_internalized_terms.size(); ++i) {
                internalize_def(m_internalized_terms[i].get());
            }
            for (unsigned i = 0; i < m_delayed_equalities.size(); ++i) {
                std::pair<theory_var, theory_var> const& eq = m_delayed_equalities[i];
                internalize_eq(eq.first, eq.second);
            }
            lbool is_sat = make_feasible();
            switch (is_sat) {
            case l_true:
                if (m_not_handled != 0) {                    
                    return FC_GIVEUP;
                }
                return FC_DONE;
            case l_false:
                failed();
                return FC_CONTINUE;
            case l_undef:
                return FC_GIVEUP;
            default:
                UNREACHABLE();
                break;
            }
            return FC_GIVEUP;
        }

        bool is_shared(theory_var v) const {
            // TBD
            return false;
        }

        bool can_propagate() {
            return m_asserted_bounds.size() > m_asserted_qhead;
        }

        void propagate() {
            if (!can_propagate()) {
                return;
            }
            while (m_asserted_qhead < m_asserted_bounds.size()) {
                lp::bound* b = m_asserted_bounds[m_asserted_qhead];
                if (!assert_bound(*b)) {
                    failed();
                    return;
                }
                ++m_asserted_qhead;
            }
            switch (make_feasible()) {
            case l_false:
                failed();
                return;
            case l_true:
                break;
            case l_undef:
                break;
            }
        }

        bool assert_bound(lp::bound& b) {
            lp::bound_kind k = b.get_bound_kind();
            theory_var v = b.get_var();
            lp::inf_numeral const& val = b.get_value();
            switch (k) {
            case lp::lower_t:
                m_replay_bounds.push_back(lp::replay_bound(v, m_lower[v], k));
                // TBD: m_solver->set_low_bound(v, val);
                m_lower[v] = val;
                ++m_stats.m_assert_lower;
                break;
            case lp::upper_t:
                m_replay_bounds.push_back(lp::replay_bound(v, m_upper[v], k));
                // TBD: m_solver->set_upper_bound(v, val);
                m_upper[v] = val;
                ++m_stats.m_assert_upper;
                break;
            }
            return true;
        }

        lbool make_feasible() {
            lean::lp_status status = m_solver->check();
            switch (status) {
            case lean::lp_status::INFEASIBLE:
                return l_false;
            case lean::lp_status::FEASIBLE:
            case lean::lp_status::OPTIMAL:
                return l_true;
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

        void failed() {
            m_eqs.reset();
            m_core.reset();
            m_evidence.reset();
            m_solver->get_infeasibility_evidence(m_evidence);
            TRACE("arith",
            for (unsigned i = 0; i < m_evidence.size(); ++i) {                
                expr_ref e(m);
                if (m_evidence[i].first.is_zero()) { 
                    continue;
                }
                unsigned idx = m_evidence[i].second;
                switch (m_constraint_sources[idx]) {
                case inequality_source: 
                    ctx().literal2expr(m_inequalities[idx], e);
                    tout << e << "\n";
                    break;
                case equality_source: 
                    tout << mk_pp(m_equalities[idx].first->get_owner(), m) << " = " 
                         << mk_pp(m_equalities[idx].second->get_owner(), m) << "\n"; 
                    break;
                case definition_source:
                    tout << "def: " << m_definitions[idx] << ": " << mk_pp(th.get_enode(m_definitions[idx])->get_owner(), m) << "\n";
                    break;
                }
            });
            for (unsigned i = 0; i < m_evidence.size(); ++i) {                
                if (m_evidence[i].first.is_zero()) { 
                    continue;
                }
                unsigned idx = m_evidence[i].second;
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
                        th.get_id(), ctx().get_region(), 
                        m_core.size(), m_core.c_ptr(), 
                        m_eqs.size(), m_eqs.c_ptr(), 0, 0)));
        }

        justification * why_is_diseq(theory_var v1, theory_var v2) {
            return 0;
        }

        void reset_eh() {
            m_arith_eq_adapter.reset_eh();
            m_stats.reset();
            m_solver = 0;
            m_scopes.reset();
            // 
        }

        void init_model(model_generator & mg) {
            m_variable_values.clear();
            m_solver->get_model(m_variable_values);
            m_factory = alloc(arith_factory, m);
            mg.register_factory(m_factory);
        }

        model_value_proc * mk_value(enode * n, model_generator & mg) {
            bool is_int = a.is_int(n->get_owner());
            theory_var v = n->get_th_var(th.get_id());
            SASSERT(v != null_theory_var);
            SASSERT(v < static_cast<theory_var>(m_theory_var2var_index.size()));
            SASSERT(UINT_MAX != m_theory_var2var_index[v]);
            rational num = m_variable_values[m_theory_var2var_index[v]];
            return alloc(expr_wrapper_proc, m_factory->mk_value(num, is_int));
        }

        bool get_value(enode* n, expr_ref& r) {
            theory_var v = n->get_th_var(th.get_id());            
            if (null_theory_var == v) return false;
            if (v >= static_cast<theory_var>(m_theory_var2var_index.size())) return false;
            rational num = m_variable_values[m_theory_var2var_index[v]];
            bool is_int = a.is_int(n->get_owner()); 
            r = a.mk_numeral(num, is_int);
            return true;
        }
    

        bool validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const {
            rational num1 = m_variable_values[m_theory_var2var_index[v1]];
            rational num2 = m_variable_values[m_theory_var2var_index[v2]];
            return (num1 == num2) == is_true;
        }

        void display(std::ostream & out) const {
            if (m_solver) {
                m_solver->print_constraints(out);
            }
        }

        void collect_statistics(::statistics & st) const {
            m_arith_eq_adapter.collect_statistics(st);
            // TBD: 
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
