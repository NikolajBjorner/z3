/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/linear_combination_iterator.h"
namespace lean {
template <typename T>
struct iterator_on_indexed_vector:linear_combination_iterator<T> {
    const indexed_vector<T> & m_v;
    unsigned m_offset = 0;
    iterator_on_indexed_vector(const indexed_vector<T> & v) : m_v(v){}
    bool next(T & a, unsigned & i) {
        if (m_offset >= m_v.m_index.size())
            return false;
        i = m_v.m_index[m_offset++];
        a = m_v.m_data[i];
        return true;
    }
    void reset() {
        m_offset = 0;
    }
    linear_combination_iterator<T>* clone() {
        return new iterator_on_indexed_vector(m_v);
    }
};
}
