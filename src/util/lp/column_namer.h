#pragma once
/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <string>
#include "util/lp/linear_combination_iterator.h"
namespace lean {
class column_namer {
public:
    virtual std::string get_column_name(unsigned j) const = 0;
    template <typename T>
    void print_linear_iterator(const linear_combination_iterator<T> & it, std::ostream & out) {
        std::vector<std::pair<T, unsigned>> coeff;
        T a;
        unsigned i;
        while (it.next(a, i)) {
            coeff.emplace_back(a, i);
        }
        print_linear_combination_of_column_indices(coeff, out);
    }
    template <typename T>
    void print_linear_combination_of_column_indices(const std::vector<std::pair<T, unsigned>> & coeffs, std::ostream & out) const {
    bool first = true;
    for (const auto & it : coeffs) {
        auto val = it.first;
        if (first) {
            first = false;
        } else {
            if (numeric_traits<T>::is_pos(val)) {
                out << " + ";
            } else {
                out << " - ";
                val = -val;
            }
        }
        if (val != numeric_traits<T>::one())
            out << T_to_string(val);
        out << get_column_name(it.second);
    }
}

};
}
