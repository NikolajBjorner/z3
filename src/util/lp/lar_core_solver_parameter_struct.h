/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <string>
#include "util/lp/lp_settings.h"
#include "util/lp/stacked_value.h"
#include "util/lp/stacked_map.h"
namespace lean {
template <typename T, typename X>
struct lar_core_solver_parameter_struct {
    stacked_value<std::vector<X>> m_x; // the solution
    stacked_value<std::vector<column_type>> m_column_types;
    stacked_value<std::vector<X>> m_low_bounds;
    stacked_value<std::vector<X>> m_upper_bounds;
    stacked_value<std::vector<unsigned>> m_basis;
    static_matrix<T, X> m_A;
    lp_settings m_settings;
    stacked_map<unsigned, std::string> m_column_names;
    void push() {
        m_x.push();
        m_column_types.push();
        m_low_bounds.push();
        m_upper_bounds.push();
        m_basis.push();
        m_A.push();
        m_column_names.push();
    }
    void pop() {
        pop(1);
    }
    void pop(unsigned k) {
        m_x.pop(k);
        m_column_types.pop(k);
        m_low_bounds.pop(k);
        m_upper_bounds.pop(k);
        m_basis.pop(k);
        m_A.pop(k);
        m_column_names.pop(k);
    }
};
}
