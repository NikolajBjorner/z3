
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
            assert_body_axiom(e);
        }
        m_q_body_expand.clear();
    }

    // if `is_true` and `v = C_f_i(t1…tn)`, then body-expand i-th case of `f(t1…tn)`
    void theory_recfun::assign_eh(bool_var v, bool is_true) {
        // TODO: find if `v` is a case_pred
    }

     // replace `vars` by `args` in `e`
    expr_ref&& theory_recfun::apply_args(recfun::vars const & vars,
                                    ptr_vector<expr> const & args,
                                    expr * e) {
        // check that var order is standard
        SASSERT(vars.size() == 0 || vars[vars.size()-1].get_idx() == 0);
        var_subst subst(m(), true);
        expr_ref new_body(m());
        subst(e, args.size(), args.c_ptr(), new_body);
        get_context().get_rewriter()(new_body); // simplify
        return std::move(new_body);
    }
    
    void theory_recfun::assert_macro_axiom(case_expansion & e) {
        TRACE("recfun", tout << "assert_macro_axiom" << pp_case_expansion(e););
        SASSERT(e.m_def->is_fun_macro());
        expr * lhs = e.m_lhs;
        context & ctx = get_context();
        auto & vars = e.m_def->get_vars();
        // substitute `e.args` into the macro RHS
        expr * rhs = apply_args(vars, e.m_args, e.m_def->get_macro_rhs());
        TRACE("recfun", tout << "macro expansion yields" << mk_pp(rhs,m()););
        // now build the axiom `lhs = rhs`
        ctx.internalize(rhs, false);
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
            enode * e_lhs = ctx.get_enode(lhs);
            enode * e_rhs = ctx.get_enode(rhs);
            // TODO: proper justification
            //justification * js = ctx.mk_justification(
            ctx.assign_eq(e_lhs, e_rhs, eq_justification());
        }   
    }

    void theory_recfun::assert_case_axioms(case_expansion & e) {
        TRACE("recfun", tout << "assert_case_axioms" << pp_case_expansion(e););
        SASSERT(e.m_def->is_fun_defined());
        // TODO: add axioms for all cases paths
        // TODO: also body-expand paths that do not depend on any defined fun
    }

    void theory_recfun::assert_body_axiom(body_expansion & e) {
        TRACE("recfun", tout << "assert_body_axioms" << pp_body_expansion(e););
        context & ctx = get_context();
        auto & vars = e.m_cdef->get_def()->get_vars();
        auto & args = e.m_args;
        // check that var order is standard
        SASSERT(vars.size() == 0 || vars[vars.size()-1].get_idx() == 0);
        expr_ref lhs(u().mk_fun_defined(args), m());
        // substitute `e.args` into the RHS of this particular case
        expr_ref rhs = apply_args(vars, args, e.m_cdef->get_rhs());
        // substitute `e.args` into the guard of this particular case, to make
        // the `condition` part of the clause `conds => lhs=rhs`
        ref_vector<expr, ast_manager> guards(m());
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref new_guard = apply_args(vars, args, g);
            guards.push_back(new_guard);
        }
        // now build the axiom `conds => lhs = rhs`
        TRACE("recfun", tout << "adding axiom:\n" << mk_pp(lhs, m())
              << "\n=\n" << mk_pp(rhs, m()) << "\n<=\n";
              for (auto& g : conds) tout << mk_pp(g,m()) << "\n";
              tout << "\n";);
        ctx.internalize(rhs, false);
        for (auto& g : guards) ctx.internalize(g, false);
        if (m().proofs_enabled()) {
            // add unit clause `conds => lhs=rhs`
            svector<literal> clause(guards.size() + 1);
            for (auto& g : guards) {
                ctx.internalize(g, false);
                literal l = ~ ctx.get_literal(g);
                ctx.mark_as_relevant(l);
                clause.push_back(l);
            }
            literal l(mk_eq(lhs, rhs, true));
            ctx.mark_as_relevant(l);
            clause.push_back(l);
            ctx.mk_th_axiom(get_id(), clause.size(), clause.c_ptr());
        }
        else {
            region r;
            enode * e_lhs = ctx.get_enode(lhs);
            enode * e_rhs = ctx.get_enode(rhs);
            // TODO: proper justification
            //justification * js = ctx.mk_justification(
            ctx.assign_eq(e_lhs, e_rhs, eq_justification());
        }   
    }

    void theory_recfun::add_theory_assumptions(expr_ref_vector & assumptions) {
        TRACE("recfun", tout << "add_theory_assumptions";);
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
