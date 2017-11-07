/*++
Module Name:

    recfun_decl_plugin.cpp

Abstract:

    Declaration and definition of (potentially recursive) functions

Author:

    Simon Cruanes 2017-11

Revision History:

--*/

#include "ast/recfun_decl_plugin.h"

namespace recfun {
    
    def::def(symbol s, ast_manager &m, sort* args, unsigned n_args, sort* ret):
        m_name(s), m_arg_sorts(m), m_ret_sort(ret, m), m_cases() {
        for (auto i=0; i<n_args; ++i) {
            sort_ref s(&args[i], m);
            m_arg_sorts.push_back(s);
        }
    }

}