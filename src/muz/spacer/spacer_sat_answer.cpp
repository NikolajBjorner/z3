#include "muz/spacer/spacer_sat_answer.h"
#include "muz/base/dl_context.h"
#include "muz/base/dl_rule.h"

#include "smt/smt_solver.h"

namespace spacer {

struct ground_sat_answer_op::frame {
    reach_fact *m_rf;
    pred_transformer &m_pt;
    expr_ref_vector m_gnd_subst;
    expr_ref m_gnd_eq;
    expr_ref m_fact;
    unsigned m_visit;
    expr_ref_vector m_kids;

    frame(reach_fact *rf, pred_transformer &pt, const expr_ref_vector &gnd_subst) :
        m_rf(rf), m_pt(pt),
        m_gnd_subst(gnd_subst),
        m_gnd_eq(pt.get_ast_manager()),
        m_fact(pt.get_ast_manager()),
        m_visit(0),
        m_kids(pt.get_ast_manager()) {

        ast_manager &m = pt.get_ast_manager();
        spacer::manager &pm = pt.get_manager();

        m_fact = m.mk_app(head(), m_gnd_subst.size(), m_gnd_subst.c_ptr());
        if (pt.head()->get_arity() == 0)
            m_gnd_eq = m.mk_true();
        else {
            SASSERT(m_gnd_subst.size() == pt.head()->get_arity());
            for (unsigned i = 0, sz = pt.sig_size(); i < sz; ++i) {
                m_gnd_eq = m.mk_eq(m.mk_const(pm.o2n(pt.sig(i), 0)),
                                      m_gnd_subst.get(i));
            }
        }
    }

    func_decl* head() {return m_pt.head();}
    expr* fact() {return m_fact;}
    const datalog::rule &rule() {return m_rf->get_rule();}
    pred_transformer &pt() {return m_pt;}
};

ground_sat_answer_op::ground_sat_answer_op(context &ctx) :
    m_ctx(ctx), m(m_ctx.get_ast_manager()), m_pm(m_ctx.get_manager()),
    m_pinned(m) {
    m_solver = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
}

proof_ref ground_sat_answer_op::operator()(pred_transformer &query) {


    vector<frame> todo;

    // -- find substitution for a query if query is not nullary
    expr_ref_vector qsubst(m);
    if (query.head()->get_arity() > 0) {
        solver::scoped_push _s_(*m_solver);
        m_solver->assert_expr(query.get_last_rf()->get());
        lbool res = m_solver->check_sat(0, nullptr);
        (void)res;
        SASSERT(res == l_true);
        model_ref mdl;
        m_solver->get_model(mdl);
        for (unsigned i = 0, sz = query.sig_size(); i < sz; ++i) {
            expr_ref arg(m), val(m);
            arg = m.mk_const(m_pm.o2n(query.sig(i), 0));
            mdl->eval(arg, val, true);
            qsubst.push_back(val);
        }
    }

    frame root(query.get_last_rf(), query, qsubst);
    todo.push_back(root);

    while (!todo.empty()) {
        frame &curr = todo.back();
        if (m_cache.contains(curr.fact()))
        {
            todo.pop_back();
            continue;
        }

        if (curr.m_visit == 0) {
            mk_children(curr, todo);
            curr.m_visit = 1;
        }
        else {
            proof* pf = mk_proof_step(curr);
            m_cache.insert(curr.fact(), pf);
            todo.pop_back();
        }

    }
    return proof_ref(m_cache.find(root.fact()), m);
}


void ground_sat_answer_op::mk_children(frame &fr, vector<frame> &todo) {
    const datalog::rule &r = fr.rule();
    ptr_vector<func_decl> preds;
    fr.pt().find_predecessors(r, preds);

    if (preds.empty()) return;

    const reach_fact_ref_vector &kid_rfs = fr.m_rf->get_justifications();
    solver::scoped_push _s_(*m_solver);
    m_solver->assert_expr(fr.m_gnd_eq);
    unsigned ut_sz = r.get_uninterpreted_tail_size();
    for (unsigned i = 0; i < ut_sz; ++i) {
        expr_ref f(m);
        m_pm.formula_n2o(kid_rfs.get(i)->get(), f, i);
        m_solver->assert_expr(f);
    }
    m_solver->assert_expr(fr.pt().transition());
    m_solver->assert_expr(fr.pt().rule2tag(&r));

    lbool res = m_solver->check_sat(0, nullptr);
    (void)res;
    SASSERT(res == l_true);

    model_ref mdl;
    m_solver->get_model(mdl);
    expr_ref_vector subst(m);
    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) {
        subst.reset();
        mk_child_subst_from_model(preds.get(i), i, mdl, subst);
        todo.push_back(frame(kid_rfs.get(i),
                             m_ctx.get_pred_transformer(preds.get(i)), subst));
        fr.m_kids.push_back(todo.back().fact());
    }
}


void ground_sat_answer_op::mk_child_subst_from_model(func_decl *pred,
                                                      unsigned j, model_ref &mdl,
                                                      expr_ref_vector &subst) {
    pred_transformer &pt = m_ctx.get_pred_transformer(pred);
    for (unsigned i = 0, sz = pt.sig_size(); i < sz; ++i) {
        expr_ref arg(m), val(m);
        arg = m.mk_const(m_pm.o2o(pt.sig(i), 0, j));
        mdl->eval(arg, val, true);
        subst.push_back(val);
    }
}

proof *ground_sat_answer_op::mk_proof_step(frame &fr) {
    svector<std::pair<unsigned, unsigned>> positions;
    vector<expr_ref_vector> substs;

    proof_ref_vector premises(m);
    datalog::rule_manager &rm = m_ctx.get_datalog_context().get_rule_manager();
    expr_ref rule_fml(m);
    rm.to_formula(fr.rule(), rule_fml);
    premises.push_back(m.mk_asserted(rule_fml));
    for (auto &k : fr.m_kids) {premises.push_back(m_cache.find(k));}

    m_pinned.push_back(m.mk_hyper_resolve(premises.size(),
                                          premises.c_ptr(),
                                          fr.fact(),
                                          positions, substs));
    return to_app(m_pinned.back());
}

}
