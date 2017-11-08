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
        OP_FUN_MACRO, // unfold eagerly, only one case
        OP_FUN_DEFINED, // defined function with multiple cases, possibly recursive
        OP_FUN_CASE_PRED, // predicate guarding a given control flow path
    };

    /*! A predicate `p(t1…tn)`, that, if true, means `f(t1…tn)` is following
        a given path of its control flow and can be unrolled.

        For example, `fact n := if n<2 then 1 else n * fact(n-1)` would have two cases,
        and therefore two case predicates `C_fact_0` and `C_fact_1`, where
        `C_fact_0(t)=true` means `t<2` (first path) and `C_fact_1(t)=true` means `¬(t<2)` (second path).
    */
    class case_pred {
        friend class case_def;
        symbol                      m_name; // symbol for the predicate
        std::string                 m_name_buf; // memory for m_name
        sort_ref_vector const &     m_arg_sorts;

        case_pred(sort_ref_vector const & args) : m_name(), m_name_buf(), m_arg_sorts(args) {}
        void set_name(std::string & s);
    public:
        symbol const & name() const { return m_name; }
        sort_ref_vector const & args() const { return m_arg_sorts; }
    };

    class case_def {
        friend class def;
        case_pred           m_pred; //<! predicate used for this case
        vector<expr_ref>    m_guards; //<! conjunction that is equivalent to this case
        expr_ref            m_rhs; //<! if guard is true, `f(t1…tn) = rhs` holds

        case_def(ast_manager & m,
                 std::string & name,
                 sort_ref_vector const & arg_sorts,
                 expr* guards,
                 unsigned num_guards,
                 expr* rhs);

        void add_guard(expr_ref && e) { m_guards.push_back(e); }
    public:
        case_pred const & pred() const { return m_pred; }
        vector<expr_ref> const & guards() const { return m_guards; }
        expr * guards_c_ptr() const { return *m_guards.c_ptr(); }
        expr * guard(unsigned i) const { return m_guards[i]; }
        expr * rhs() const { return m_rhs; }
        unsigned num_guards() const { return m_guards.size(); }
    };

    class def {
        friend class util;
        typedef ptr_vector<var>  vars;
        typedef vector<case_def> cases;
        op_kind             m_kind; //<! kind of function
        ast_manager &       m_manager;
        symbol              m_name; //<! name of function
        sort_ref_vector     m_arg_sorts; //<! type of arguments
        sort_ref            m_ret_sort; //<! return type
        vars                m_vars; //<! variables of the function
        cases               m_cases; //!< possible cases

        ast_manager & m() const { return m_manager; }
        symbol const & name() const { return m_name; }
        sort_ref_vector const & sort_args() const { return m_arg_sorts; }
        sort_ref const & sort_ret() const { return m_ret_sort; }
        def(ast_manager &m, symbol s, sort* args, unsigned n_args, sort* ret);

        // compute cases for a function, given its RHS (possibly containing `ite`).
        void compute_cases(var * vars, unsigned n_vars, expr* rhs);

        bool contains_ite(expr* e); // expression contains a test?
    public:
        vars const & get_vars() const { return m_vars; }
        cases const & get_cases() const { return m_cases; }
    };

    // TODO: decl_plugin?
    
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

        // Add a function declaration (TODO: allow mutual definitions)
        void add_fun(symbol s, sort * args, unsigned n_args, var * vars, unsigned n_vars, expr * rhs);
    };

}
