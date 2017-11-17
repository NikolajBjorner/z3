/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_recfun.h

Abstract:

    Theory responsible for unrolling recursive functions

Author:

    Leonardo de Moura (leonardo) 2008-10-31.

Revision History:

--*/
#ifndef THEORY_RECFUN_H_
#define THEORY_RECFUN_H_

#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/ast_ll_pp.h"

namespace smt {

    class theory_recfun : public theory {
        typedef trail_stack<theory_recfun>  th_trail_stack;

        struct stats {
            unsigned m_case_expansions, m_body_expansions, m_macro_expansions;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };

        // one case-expansion of `f(t1…tn)`
        struct case_expansion {
            expr *              m_lhs; // the term to expand
            recfun_def *        m_def;
            ptr_vector<expr>    m_args;
            case_expansion(recfun_util& u,app * n)
                : m_lhs(n), m_def(0), m_args()
            {
                SASSERT(u.is_defined_or_macro(n));
                func_decl * d = n->get_decl();
                const symbol& name = d->get_name();
                m_def = &u.get_def(name);
                m_args.reserve(n->get_num_args());
                m_args.append(n->get_num_args(), n->get_args());
            }
            case_expansion(case_expansion const & from)
                : m_lhs(from.m_lhs),
                  m_def(from.m_def),
                  m_args(from.m_args) {}
            case_expansion(case_expansion && from)
                : m_lhs(from.m_lhs),
                  m_def(from.m_def),
                  m_args(std::move(from.m_args)) {}
        };

        struct pp_case_expansion {
            case_expansion & e;
            ast_manager & m;
            pp_case_expansion(case_expansion & e, ast_manager & m) : e(e), m(m) {}
            std::ostream& operator<<(std::ostream & out) const {
                return out << "case_exp(" << mk_bounded_pp(e.m_lhs, m) << ")";
            }
        };

        // one body-expansion of `f(t1…tn)` using a `C_f_i(t1…tn)`
        struct body_expansion {
            recfun_case_def *   m_cdef;
            ptr_vector<expr>    m_args;

            body_expansion(recfun_util& u, app * n) : m_cdef(0), m_args() {
                SASSERT(u.is_case_pred(n));
                func_decl * d = n->get_decl();
                const symbol& name = d->get_name();
                m_cdef = &u.get_case_def(name);
                m_args.reserve(n->get_num_args());
                m_args.append(n->get_num_args(), n->get_args());
            }
            body_expansion(body_expansion const & from): m_cdef(from.m_cdef), m_args(from.m_args) {}
            body_expansion(body_expansion && from) : m_cdef(from.m_cdef), m_args(std::move(from.m_args)) {}
        };

        struct pp_body_expansion {
            body_expansion & e;
            ast_manager & m;
            pp_body_expansion(body_expansion & e, ast_manager & m) : e(e), m(m) {}
            
            std::ostream& operator<<(std::ostream & out) const {
                out << "body_exp(" << e.m_cdef->get_name();
                for (auto* t : e.m_args) {
                    out << " " << mk_bounded_pp(t,m);
                }
                return out << ")";
            }
        };

        recfun_util         m_util;
        stats               m_stats;
        th_trail_stack      m_trail;

        vector<case_expansion>      m_q_case_expand;
        vector<body_expansion>      m_q_body_expand;

        recfun_util & u() { return m_util; }
        ast_manager & m() { return get_manager(); }
        bool is_defined(app * f) const { return m_util.is_defined(f); }
        bool is_macro(app * f) const { return m_util.is_macro(f); }
        bool is_case_pred(app * f) const { return m_util.is_case_pred(f); }

        bool is_defined(enode * e) const { return is_defined(e->get_owner()); }
        bool is_macro(enode * e) const { return is_macro(e->get_owner()); }
        bool is_case_pred(enode * e) const { return is_case_pred(e->get_owner()); }

        void reset_queues();
        expr_ref&& apply_args(recfun::vars const & vars, ptr_vector<expr> const & args, expr * e);
        void assert_macro_axiom(case_expansion & e);
        void assert_case_axioms(case_expansion & e);
        void assert_body_axiom(body_expansion & e);
    protected:
        void push_case_expand(case_expansion&& e) { m_q_case_expand.push_back(e); }
        void push_body_expand(body_expansion&& e) { m_q_body_expand.push_back(e); }

        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void reset_eh();
        void relevant_eh(app * n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        bool can_propagate() override;
        void propagate() override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void add_theory_assumptions(expr_ref_vector & assumptions) override;

    public:
        theory_recfun(ast_manager & m);
        virtual ~theory_recfun() override;
        virtual theory * mk_fresh(context * new_ctx);
        virtual void display(std::ostream & out) const override;
        virtual void collect_statistics(::statistics & st) const override;
    };

}

#endif
