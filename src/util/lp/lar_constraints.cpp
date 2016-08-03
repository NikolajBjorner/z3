/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#include <utility>
#include "util/lp/lar_constraints.h"
namespace lean {

lar_constraint::lar_constraint(const std::vector<std::pair<mpq, var_index>> & left_side, lconstraint_kind kind, mpq right_side) :  lar_base_constraint(kind, right_side) {
    for (auto & it : left_side) {
        auto r = m_left_side_map_from_index_to_coefficient.find(it.second);
        if (r == m_left_side_map_from_index_to_coefficient.end()) {
            m_left_side_map_from_index_to_coefficient[it.second] = it.first;
        } else {
            r->second += it.first;
        }
    }
}

lar_constraint::lar_constraint(const lar_base_constraint & c): lar_base_constraint(c.m_kind, c.m_right_side) {
    for (auto t : c.get_left_side_coefficients())
        m_left_side_map_from_index_to_coefficient.insert(std::make_pair(t.second, t.first));
}


std::vector<std::pair<mpq, var_index>> lar_constraint::get_left_side_coefficients() const {
    std::vector<std::pair<mpq, var_index>> ret;
    for (auto it : m_left_side_map_from_index_to_coefficient) {
        ret.push_back(std::make_pair(it.second, it.first));
    }
    return ret;
}

std::vector<std::pair<mpq, var_index>> lar_normalized_constraint::get_left_side_coefficients() const {
    std::vector<std::pair<mpq, var_index>> ret;
    for (auto t : m_canonic_left_side.m_coeffs) ret.push_back(t);
    return ret;
}
}






