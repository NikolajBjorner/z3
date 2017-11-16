
#include "util/stats.h"
#include "smt/theory_recfun.h"

namespace smt {

    theory_recfun::theory_recfun(ast_manager & m)
        : theory(m.mk_family_id("recfun")), m_util(m), m_trail(*this),
          m_q_case_expand(), m_q_body_expand()
        {}

    theory_recfun::~theory_recfun() {}

    theory* theory_recfun::mk_fresh(context* new_ctx) {
        return alloc(theory_recfun, new_ctx->get_manager());
    }

    bool theory_recfun::internalize_atom(app * atom, bool gate_ctx) {
        return internalize_term(atom);
    }

    bool theory_recfun::internalize_term(app * term) {
        TRACE("recfun", tout << "internalizing term:\n" << mk_pp(term, m()) << "\n";);
        context & ctx = get_context();
        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);
        // the internalization of the arguments may have triggered the internalization of term.
        if (ctx.e_internalized(term))
            return true;
        ctx.internalize(term, false);
        return true;
    }

    void theory_recfun::reset_queues() {
        m_q_case_expand.reset();
        m_q_body_expand.reset();
    }

    void theory_recfun::reset_eh() {
        m_trail.reset();
        reset_queues();   
    }

    /*
     * when `n` becomes relevant, if it's `f(t1…tn)` with `f` defined,
     * then case-expand `n`. If it's a macro we can also immediately
     * body-expand it.
     */
    void theory_recfun::relevant_eh(app * n) {
        TRACE("recfun", tout << "relevant_eh: " << mk_bounded_pp(n, m()()) << "\n";);
        context & ctx = get_context();
        SASSERT(ctx.relevancy());
        if (u().is_defined_or_macro(n)) {
            TRACE("recfun", tout << "relevant_eh: (defined)" << n->get_id() << mk_bounded_pp(n, get_manager()) << "\n";);
            case_expansion e(u(), n);
            push_case_expand(std::move(e));
        }
    }

    void theory_recfun::push_scope_eh() {
        theory::push_scope_eh();
        m_trail.push_scope();
    }

    void theory_recfun::pop_scope_eh(unsigned num_scopes) {
        m_trail.pop_scope(num_scopes);
        theory::pop_scope_eh(num_scopes);
        reset_queues();
    }
    
    void theory_recfun::restart_eh() {
        m_trail.reset();
        reset_queues();
    }

    bool theory_recfun::can_propagate() {
        return ! (m_q_case_expand.empty() && m_q_body_expand.empty());
    }

    void theory_recfun::propagate() {
        TRACE("recfun", tout << "propagate");
        for (case_expansion & e : m_q_case_expand) {
            if (e.m_def->is_fun_macro()) {
                // body expand immediately
                assert_macro_axiom(e);
            } else {
                // case expand
                SASSERT(e.m_def->is_fun_defined());
                assert_case_axioms(e);                
            }
        }
        m_q_case_expand.clear();

        for (body_expansion & e : m_q_body_expand) {
            assert_body_axioms(e);
        }
        m_q_body_expand.clear();
    }
    
    void theory_recfun::assert_macro_axiom(case_expansion & e) {
        TRACE("recfun", tout << "assert_macro_axiom" << e;);
        SASSERT(e.m_def->is_fun_macro());
        expr * lhs = e.m_lhs;
        context & ctx = get_context();
        auto & vars = e.m_def->get_vars();
        // check that var order is standard
        SASSERT(vars.size() == 0 || vars[vars.size()-1].get_idx() == 0);
        // substitute `e.args` into the macro RHS
        var_subst subst(m(), true);
        expr_ref new_body(m());
        subst(e.m_def->get_macro_rhs(), e.m_args.size(), e.m_args.c_ptr(), new_body);
        expr * rhs = new_body.get();
        TRACE("recfun", tout << "macro expansion yields" << mk_pp(rhs,m()););
        // now build the axiom `lhs = new_body`
        ctx.internalize(new_body.get(), false);
        TRACE("recfun", tout << "adding axiom:\n" << mk_pp(lhs, m()) << "\n=\n" << mk_pp(rhs, m()) << "\n";);
        if (m().proofs_enabled()) {
            // add unit clause `lhs=rhs`
            literal l(mk_eq(lhs, rhs, true));
            ctx.mark_as_relevant(l);
            literal lits[1] = {l};
            ctx.mk_th_axiom(get_id(), 1, lits);
        }
        else {
            region r;
            enode * _lhs = ctx.get_enode(lhs);
            enode * _rhs = ctx.get_enode(rhs);
            // TODO: proper justification
            //justification * js = ctx.mk_justification(
            ctx.assign_eq(_lhs, _rhs, eq_justification());
        }   
    }

    void theory_recfun::assert_case_axioms(case_expansion & e) {
        SASSERT(e.m_def->is_fun_defined());
        // TODO: add axioms for all cases paths
    }

    void theory_recfun::assert_body_axioms(body_expansion & e) {
        // TODO: add axioms for this case's body
    }

    void theory_recfun::add_theory_assumptions(expr_ref_vector & assumptions) {
        // TODO: add depth-limit assumptions?
    }

    void theory_recfun::display(std::ostream & out) const {
        out << "recfun{}";
    }

    void theory_recfun::collect_statistics(::statistics & st) const {
        st.update("recfun macro expansion", m_stats.m_macro_expansions);
        st.update("recfun case expansion", m_stats.m_case_expansions);
        st.update("recfun body expansion", m_stats.m_body_expansions);
    }
}
