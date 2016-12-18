/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
namespace lean {
struct lar_term {
    // the term evaluates to sum of m_coeffs + m_v
    std::unordered_map<unsigned, mpq> m_coeffs;
    mpq m_v;
    lar_term() {}
    void add_to_map(unsigned j, const mpq& c) {
        auto it = m_coeffs.find(j);
        if (it == m_coeffs.end()) {
            m_coeffs.emplace(j, c);
        } else {
            it->second += c;
            if (is_zero(it->second))
                m_coeffs.erase(it);
        }
    }
    lar_term(const std::vector<std::pair<mpq, unsigned>> coeffs,
             const mpq & v) : m_v(v) {
        for (const auto & p : coeffs) {
            add_to_map(p.second, p.first);
        }
    }
    bool operator==(const lar_term & a) const {  return false; } // take care not to create identical terms
    bool operator!=(const lar_term & a) const {  return ! (*this == a);}
    // some terms get used in add constraint
    // it is the same as the offset in the m_normalized_constraints

    std::vector<std::pair<mpq, unsigned>> coeffs_as_vector() const {
        std::vector<std::pair<mpq, unsigned>> ret;
        for (const auto & p :  m_coeffs) {
            ret.emplace_back(p.second, p.first);
        }
        return ret;
    }

    // j is the basic variable to substitute
    void subst(unsigned j, linear_combination_iterator<mpq> & li) {
        unsigned it_j;
        mpq a;

        auto it = m_coeffs.find(j);
        if (it == m_coeffs.end()) return;
        const mpq & b = it->second;
        while (li.next(a, it_j)) {
            if (it_j == j)
                continue;

            add_to_map(it_j, - b * a);
        }
        
        m_coeffs.erase(it);
    }
    
    bool contains(unsigned j) const {
        return m_coeffs.find(j) != m_coeffs.end();
    }
};
}
