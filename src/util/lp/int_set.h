/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include "util/lp/indexed_vector.h"
#include <ostream>
namespace lean {
// serves at a set of non-negative integers smaller than the set size
class int_set {
    std::vector<int> m_data;
public:
    std::vector<int> m_index;
    int_set(unsigned size): m_data(size, -1) {}
    bool contains(unsigned j) const {
        if (j >= m_data.size())
            return false;
        return m_data[j] >= 0;
    }
    void insert(unsigned j) {
        lean_assert(j < m_data.size());
        if (contains(j)) return;
        m_data[j] = m_index.size();
        m_index.push_back(j);
    }
    void erase(unsigned j) {
        if (!contains(j)) return;
        unsigned pos_j = m_data[j];
        unsigned last_pos = m_index.size() - 1;
        int last_j = m_index[last_pos];
        if (last_pos != pos_j) {
            // move last to j spot
            m_data[last_j] = pos_j;
            m_index[pos_j] = last_j;
        }
        m_index.pop_back();
        m_data[j] = -1;
    }

    void resize(unsigned size) {
        m_data.resize(size, -1);
    }
    
    unsigned size() const { return m_index.size();}
    bool is_empty() const { return size() == 0; }
    void clear() {
        for (unsigned j : m_index)
            m_data[j] = -1;
        m_index.clear();
    }
    void print(std::ostream & out ) const {
        for (unsigned j : m_index) {
            out << j << " ";
        }
        out << std::endl;
    }
};
}
