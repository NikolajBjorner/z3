/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <string>
#include <algorithm>
#include <utility>
#include "util/lp/column_info.h"
namespace lean {

    enum lconstraint_kind {
        LE = -2, LT = -1 , GE = 2, GT = 1, EQ = 0
    };
    
    inline std::ostream& operator<<(std::ostream& out, lconstraint_kind k) {
        switch (k) {
        case LE: return out << "<=";
        case LT: return out << "<";
        case GE: return out << ">=";
        case GT: return out << ">";
        case EQ: return out << "=";
        }
        return out << "??";
    }

class lar_normalized_constraint; // forward definition
inline bool compare(const std::pair<mpq, var_index> & a, const std::pair<mpq, var_index> & b) {
    return a.second < b.second;
}

struct ul_pair {
    constraint_index m_low_bound_witness = static_cast<constraint_index>(-1);
    constraint_index m_upper_bound_witness = static_cast<constraint_index>(-1);
    var_index m_j = static_cast<var_index>(-1); // this is the index of the additional variable created for the constraint
    bool operator!=(const ul_pair & p) const {
        return !(*this == p);
    }

    bool operator==(const ul_pair & p) const {
        return m_low_bound_witness == p.m_low_bound_witness
            && m_upper_bound_witness == p.m_upper_bound_witness
            && m_j == p.m_j;
    }
    
    
    ul_pair(){}
    ul_pair(var_index vi) : m_j(vi) {}
    ul_pair(const ul_pair & o): m_low_bound_witness(o.m_low_bound_witness), m_upper_bound_witness(o.m_upper_bound_witness), m_j(o.m_j) {}
};

class canonic_left_side {
public:
    std::vector<std::pair<mpq, var_index>> m_coeffs;

    canonic_left_side() {}
    
    canonic_left_side(const canonic_left_side & ls): m_coeffs(ls.m_coeffs) {
    }

    canonic_left_side(std::vector<std::pair<mpq, var_index>> coeffs) {
        std::unordered_map<var_index, mpq> tmp_map;

        for (auto & it : coeffs) {
            auto r = tmp_map.find(it.second);
            if (r == tmp_map.end()) {
                tmp_map.emplace(it.second, it.first);
            } else {
                r->second += it.first;
            }
        }
        
        for (auto & it : tmp_map) {
            m_coeffs.push_back(std::pair<mpq, var_index>(it.second, it.first));
        }

        std::sort(m_coeffs.begin(), m_coeffs.end(), compare);
        normalize();
    }

    unsigned size() const { return static_cast<unsigned>(m_coeffs.size()); }

    void normalize() {
        if (m_coeffs.size() == 0) return;
        auto t = m_coeffs[0].first;
        for (auto & it : m_coeffs)
            it.first /= t;
    }

    bool operator==(const canonic_left_side& a) const {
        if (m_coeffs.size() != a.m_coeffs.size()) return false;
        for (unsigned i = 0; i < m_coeffs.size(); i++) {
            if (m_coeffs[i] != a.m_coeffs[i])
                return false;
        }
        return true;
    }

    bool operator!=(const canonic_left_side & a) const {
        return !(*this == a);
    }
    
    std::size_t hash_of_ls() const {
        std::size_t ret = 0;
        std::hash<std::pair<mpq, var_index>> hash_fun;
        for (auto & v : m_coeffs) {
            ret |= (hash_fun(v) << 2);
        }
        return ret;
    }
    template <typename T>
    T value(const std::vector<T> & x) const {
        T r = zero_of_type<T>();
        for (auto & v : m_coeffs)
            r += v.first * x[v.second];
        return r;
    }
    
};

struct hash_and_equal_of_canonic_left_side_struct {
    std::size_t operator() (const canonic_left_side& ls) const {
        return ls.hash_of_ls();
    }
    bool operator() (const canonic_left_side& a, const canonic_left_side& b) const {
        return a == b;
    }
};
}
