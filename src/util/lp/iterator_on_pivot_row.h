/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/iterator_on_indexed_vector.h"
namespace lean {
template <typename T>
struct iterator_on_pivot_row:linear_combination_iterator<T> {
    bool m_basis_returned = false;
    const indexed_vector<T> & m_v;
    unsigned m_basis_j;
    iterator_on_indexed_vector<T> m_it;
    iterator_on_pivot_row(const indexed_vector<T> & v, unsigned basis_j) : m_v(v), m_basis_j(basis_j), m_it(v) {}
    bool next(T & a, unsigned & i) {
        if (m_basis_returned == false) {
            m_basis_returned = true;
            a = one_of_type<T>();
            i = m_basis_j;
            return true;
        }
        return m_it.next(a, i);
    }
    void reset() {
        m_basis_returned = false;
        m_it.reset();
    }
    linear_combination_iterator<T> * clone() {
        iterator_on_pivot_row * r = new iterator_on_pivot_row(m_v, m_basis_j);
        return r;
    }
};
}
