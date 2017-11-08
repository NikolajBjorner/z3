/*++
Module Name:

    recfun_decl_plugin.cpp

Abstract:

    Declaration and definition of (potentially recursive) functions

Author:

    Simon Cruanes 2017-11

Revision History:

--*/

#include "ast/expr_functors.h"
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

    // Compute a set of cases, given the RHS
    void def::compute_cases(var * vars, unsigned n_vars, expr* rhs) {
        std::string name;
        name.append("case_");
        name.append(m_name.bare_str());

        for (unsigned i=0; i<n_vars; ++i) m_vars.push_back(&vars[i]);

        if (n_vars == 0 || !contains_ite(rhs)) {
            // constant function or trivial control flow, only one (dummy) case
            m_kind = OP_FUN_MACRO;
            name.append("_dummy");  
            case_def c0(m(), name, sort_args(), nullptr, 0, rhs);
            m_cases.push_back(c0);
            return;
        }

        // TODO: analyze control flow of `rhs`, building a vector of pair<guard,rhs>,
        // accumulating guards and rebuilding a `ite`-free RHS on the fly.
        // Each pair is then converted into a case_def
    }

    util::util(ast_manager & m) : m_manager(m) {}

    void util::add_fun(symbol s, sort * args, unsigned n_args, var * vars, unsigned n_vars, expr * rhs) {
        // TODO:
    }
}