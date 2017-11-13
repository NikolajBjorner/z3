/*++
Module Name:

    recfun_decl_plugin.cpp

Abstract:

    Declaration and definition of (potentially recursive) functions

Author:

    Simon Cruanes 2017-11

Revision History:

--*/

#include <sstream>
#include "ast/expr_functors.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_substitution.h"
#include "ast/recfun_decl_plugin.h"

namespace recfun {

    void case_pred::set_name(std::string & s) {
        m_name_buf = std::string(s); // owned copy
        m_name = symbol(m_name_buf.c_str());
    }

    case_def::case_def(ast_manager &m,
                       std::string & name,
                       sort_ref_vector const & arg_sorts,
                       expr* guards, unsigned num_guards, expr* rhs)
    : m_pred(arg_sorts), m_guards(), m_rhs(expr_ref(rhs,m)) {
        m_pred.set_name(name);
        for (unsigned i=0; i<num_guards; ++i) {
            m_guards.push_back(expr_ref(&guards[i], m));
        }
    }

    def::def(ast_manager &m, symbol s, sort* args, unsigned n_args, sort* ret)
        :   m_kind(OP_FUN_DEFINED), m_manager(m), m_name(s),
            m_arg_sorts(m), m_ret_sort(ret, m), m_vars(), m_cases()
    {
        for (unsigned i=0; i<n_args; ++i) m_arg_sorts.push_back(sort_ref(&args[i], m));
    }

    // does `e` contain any `ite` construct?
    bool def::contains_ite(expr * e) {
        struct ite_find_p : public i_expr_pred {
            ast_manager & m;
            ite_find_p(ast_manager & m) : m(m) {}
            virtual bool operator()(expr * e) { return m.is_ite(e); }
        };
        ite_find_p p(m());
        check_pred cp(p, m());
        return cp(e);
    }

    /*
     * compilation of functions to a list of cases
     */
    
    class compute_case_op; // fwd decl of operations called during exploration of cases
    class compute_case_alternative; // fwd decl of operations to explore alternative cases

    // state for compiling a function's definition into cases
    struct compute_case_state {
        ast_manager &               m_manager;
        region                      m_region;
        unsigned                    m_case_idx;
        expr_substitution           m_subst;
        scoped_expr_substitution    m_ssubst;
        ptr_vector<expr>            m_conditions; // current conjunction of conditions
        ptr_vector<compute_case_op> m_ops; // operations to perform during exploration
        unsigned                    m_ops_idx; // current offset in `m_ops`.
        ptr_vector<compute_case_alternative> m_alternatives; // backtrack stack

        compute_case_state(ast_manager & m)
            : m_manager(m),
              m_region(),
              m_case_idx(0),
              m_subst(m, false, false),
              m_ssubst(m_subst),
              m_ops(),
              m_ops_idx(0),
              m_alternatives()
            {}

        ast_manager &           m() { return m_manager; }
        region &                reg() { return m_region; }
        expr_substitution &     subst() { return m_subst; }
    };

    // an action (explore term, etc.) in `compute_cases`
    struct compute_case_op {
        virtual void operator()(compute_case_state & st) = 0;
        virtual void undo(compute_case_state & st) = 0;
    };

    // to explore alternative branches in `compute_cases`
    class compute_case_alternative {
        unsigned cond_size; // m_conditions.size()
        unsigned ops_idx; // m_ops_idx
        unsigned ops_size; // m_ops.size()
    public:
        compute_case_alternative(compute_case_state & st)
            : cond_size(st.m_conditions.size()),
              ops_idx(st.m_ops_idx),
              ops_size(st.m_ops.size())
              {}

        // called when backtracking; can push stuff on `ops` stack
        virtual void operator()(compute_case_state & st) {
            st.m_ops_idx = ops_idx;
            st.m_ops.shrink(ops_size);
            st.m_conditions.shrink(cond_size);
        }
    };

    // explore given term (typically, explore subterms)
    class compute_case_explore : public compute_case_op {
        expr * e;
    public:
        compute_case_explore(expr * e) : compute_case_op(), e(e) {}
        void undo(compute_case_state & st) override {}
        void operator()(compute_case_state & st) override;
    };

    class compute_case_ite_alt;

    // explore `ite a b c` by exploring `b` (resp. `c`) under condition `a` (resp. `¬a`)
    class compute_case_ite : public compute_case_op {
        ast_manager & m;
        app * e; // ite
        bool pos_case; // explore positive case or negative case?
    public:
        compute_case_ite(ast_manager & m, app * e0, bool pos_case=true)
            : compute_case_op(), m(m), e(e0), pos_case(pos_case)
            { SASSERT(m.is_ite(expr)); }

        void operator()(compute_case_state & st) override;
        void undo(compute_case_state & st) override {
            st.m_ssubst.pop(1);
        }
    };

    void compute_case_explore::operator()(compute_case_state & st) {
        if (st.m().is_ite(e)) {
            app * a = static_cast<app*>(e);
            compute_case_op * op = new (st.reg()) compute_case_ite(st.m(), a, true);
            st.m_ops.push_back(op);
        }
        else if (is_app(e)) {
            // explore all subterms
            app * a = static_cast<app*>(e);
            for (unsigned i=0; i < a->get_num_args(); ++i) {
                compute_case_op * op = new (st.reg()) compute_case_explore(a->get_arg(i));
                st.m_ops.push_back(op);
            }
        }
    }

    class compute_case_ite_alt : public compute_case_alternative {
        ast_manager & m;
        app * e;
    public:
        compute_case_ite_alt(compute_case_state & st, app* e)
            : compute_case_alternative(st), m(st.m()), e(e) {}
        virtual void operator()(compute_case_state & st) override {
            compute_case_alternative::operator()(st); // reset
            // explore negative branch
            compute_case_op * op = new (st.reg()) compute_case_ite(m, e, false);
            st.m_ops.push_back(op);
        }
    };

    void compute_case_ite::operator()(compute_case_state & st) {
        expr * cond_e = e->get_arg(0);
        expr * branch_e = pos_case ? e->get_arg(1) : e->get_arg(2);
        // prepare to undo
        if (pos_case) {
            compute_case_alternative * alt = new (st.reg()) compute_case_ite_alt(st, e);
            st.m_alternatives.push_back(alt);
        }
        // bind, then explore rhs
        compute_case_op * op = new (st.reg()) compute_case_explore(branch_e);
        st.m_ops.push_back(op);
        st.m_conditions.push_back(pos_case ? cond_e : m.mk_not(cond_e));
        st.m_ssubst.push();
        st.m_ssubst.insert(e, branch_e);
    }

    // substitute `subst` in `e`
    expr * replace_subst(ast_manager & m, expr_substitution & subst, expr * e) {
        th_rewriter rw(m);
        rw.set_substitution(&subst);
        expr_ref res(m);
        proof_ref pr(m);
        rw(e, res, pr);
        return res.get();
    }

    void def::add_case(std::string & name, expr * rhs) {
        case_def c(m(), name, sort_args(), 0, 0, rhs);
        m_cases.push_back(c);
    }
    
    // Compute a set of cases, given the RHS
    void def::compute_cases(var * vars, unsigned n_vars, expr* rhs) {
        std::string name;
        name.append("case_");
        name.append(m_name.bare_str());
        name.append("_");

        for (unsigned i=0; i<n_vars; ++i) m_vars.push_back(&vars[i]);

        if (n_vars == 0 || !contains_ite(rhs)) {
            // constant function or trivial control flow, only one (dummy) case
            m_kind = OP_FUN_MACRO;
            name.append("dummy");
            add_case(name, rhs);
            return;
        }
        
        // analyze control flow of `rhs`, accumulating guards and
        // rebuilding a `ite`-free RHS on the fly for each path in `rhs`.
        // Each such `ite`-free term is converted into a case_def and added to definition.

        compute_case_state st(m());
        compute_case_op* op0 = new (st.reg()) compute_case_explore(rhs);
        st.m_ops.push_back(op0);

        while (true) {
            // perform pending operations
            while (st.m_ops_idx < st.m_ops.size()) {
                compute_case_op* op = st.m_ops[st.m_ops_idx];
                (*op)(st);
                st.m_ops_idx ++;
            }

            // yield term `subst(rhs)` and make it into a case
            {
                expr* case_rhs = replace_subst(m(), st.m_subst, rhs);
                unsigned old_name_len = name.size();
                {   // TODO: optimize? this does many copies
                    std::ostringstream sout;
                    sout << ((unsigned long)st.m_case_idx);
                    name.append(sout.str());
                }
                st.m_case_idx ++;
                add_case(name, case_rhs);
                name.resize(old_name_len);
            }

            if (st.m_alternatives.empty()) {
                break; // done
            }
            else {
                // explore alternative
                compute_case_alternative * alt = st.m_alternatives.back();
                st.m_alternatives.pop_back();
                (*alt)(st); // will yield another expr, by pushing new ops on `m_ops`
            }
        }
    }

    /*
     * Main manager for defined functions
     */

    util::util(ast_manager & m) : m_manager(m), m_family_id() {
        // TODO: decl plugin, to obtain family_id
    }

    void util::add_fun(symbol s, sort * args, unsigned n_args, var * vars, unsigned n_vars, expr * rhs) {
        // TODO:
    }
}