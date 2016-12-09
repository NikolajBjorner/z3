/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
namespace lean {
struct lar_term {
    // the term evaluates to sum of m_coeffs + m_v
    std::vector<std::pair<mpq, unsigned>> m_coeffs;
    mpq m_v;
    lar_term() {}
    lar_term(const std::vector<std::pair<mpq, unsigned>> coeffs,
             const mpq & v) : m_coeffs(coeffs), m_v(v) {
    }
    bool operator==(const lar_term & a) const {  return m_coeffs == a.m_coeffs && m_v == a.m_v;}
    bool operator!=(const lar_term & a) const {  return ! (*this == a);}
};
}
