/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/linear_combination_iterator.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/lar_term.h"
namespace lean {
struct iterator_on_term:linear_combination_iterator<mpq> {
    unsigned m_i = 0; // the offset in term coeffs
    bool m_term_j_returned = false;
    const lar_term & m_term;
    unsigned m_term_j;
    iterator_on_term(const lar_term & t, unsigned term_j) : m_term(t), m_term_j(term_j) {}
    bool next(mpq & a, unsigned & i) {
        if (m_term_j_returned == false) {
            m_term_j_returned = true;
            a = - one_of_type<mpq>();
            i = m_term_j;
            return true;
        }
        if (m_i >= m_term.m_coeffs.size())
            return false;
        const auto & p = m_term.m_coeffs[m_i];
        a = p.first;
        i = p.second;
        m_i++;
        return true;
    }
    void reset() {
        m_term_j_returned = false;
        m_i = 0;
    }
    linear_combination_iterator<mpq> * clone() {
        iterator_on_term * r = new iterator_on_term(m_term, m_term_j);
        return r;
    }
};
}
