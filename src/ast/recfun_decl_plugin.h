/*++
Module Name:

    recfun_decl_plugin.h

Abstract:

    Declaration and definition of (potentially recursive) functions

Author:

    Simon Cruanes 2017-11

Revision History:

--*/

#pragma once

#include "ast/ast.h"

namespace recfun {
    class decl; //<! declaration of a (recursive) function, along with its definition
    class case_def; //<! one possible control path of a function
    class case_pred; //<! a predicate guarding a given control flow path of a function
    class util; //<! util for other modules

    enum op_kind {
        OP_FUN_DEFINED,
        OP_FUN_CASE_PRED,
    };

    /*! A predicate `p(t1…tn)`, that, if true, means `f(t1…tn)` is following
        a given path of its control flow and can be unrolled.

        For example, `fact n := if n<2 then 1 else n * fact(n-1)` would have two cases,
        and therefore two case predicates `C_fact_0` and `C_fact_1`, where
        `C_fact_0(t)=true` means `t<2` (first path) and `C_fact_1(t)=true` means `¬(t<2)` (second path).
    */
    class case_pred {
        friend class case_def;
        symbol              m_name; // name of the predicate
        sort_ref_vector     m_arg_sorts;

        case_pred(symbol && s, sort_ref_vector &&args) : m_name(s), m_arg_sorts(args) {}
    public:
        symbol const & name() const { return m_name; }
        sort_ref_vector const & args() const { return m_arg_sorts; }
    };

    class case_def {
        friend class decl;
        case_pred           m_pred; //<! predicate used for this case
        ptr_vector<expr>    m_guards; //<! conjunction that is equivalent to this case
        expr_ref            m_rhs; //<! if guard is true, `f(t1…tn) = rhs` holds

        case_def(ast_manager &m, expr* guards, unsigned num_guards, expr* rhs);
    public:
        case_pred const & pred() const { return m_pred; }
        expr * guards() const { return *m_guards.c_ptr(); }
        expr * guard(unsigned i) const { return m_guards[i]; }
        unsigned num_guards() const { return m_guards.size(); }
    };

    class def {
        friend class util;
        symbol              m_name; //<! name of function
        sort_ref_vector     m_arg_sorts;
        sort_ref            m_ret_sort; //<! return type
        vector<case_def>    m_cases; //!< possible cases

        def(symbol s, ast_manager &m, sort* args, unsigned n_args, sort* ret);
    public:
        vector<case_def> const & cases() const { return m_cases; }

        // compute cases for a function, given its RHS (possibly containing `ite`).
        void compute_cases(expr* rhs);
    };

    // TODO: decl_plugin
    
    // Varus utils for recursive functions
    class util {
        ast_manager &           m_manager;
        family_id               m_family_id;
        //mutable decl::plugin*   m_plugin;

        ast_manager & m() { return m_manager; }
    public:
        util(ast_manager &m);

        bool is_case_pred(app * e) const { return is_app_of(e, m_family_id, OP_FUN_CASE_PRED); }
        bool is_defined(app * e) const { return is_app_of(e, m_family_id, OP_FUN_DEFINED); }
    };

}
