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
    std::vector<X> m_x; // the solution
    std::vector<column_type> m_column_types;
    std::vector<X> m_low_bounds;
    std::vector<X> m_upper_bounds;
    std::vector<unsigned> &m_basis;
    std::vector<unsigned> &m_nbasis;
    std::vector<int> &m_heading;
    lar_core_solver_parameter_struct(    std::vector<unsigned> &basis,
                                         std::vector<unsigned> &nbasis,
                                         std::vector<int> &heading) :
        m_basis(basis),
        m_nbasis(nbasis),
        m_heading(heading) {}


    static_matrix<T, X> m_A;
    lp_settings m_settings;
    void push() {
        m_A.push();
    }
    void pop() {
        pop(1);
    }
    void pop(unsigned k) {
        m_A.pop(k);
    }
};
}
