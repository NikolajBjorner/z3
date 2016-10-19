/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/lp_settings.h"
#include "util/lp/lar_constraints.h"
namespace lean {
template <typename T>
struct bound_signature {
    T m_coeff;
    unsigned m_i;
    bool m_low_bound;
    bound_signature(const T& coeff, unsigned i, bool at_low) : m_coeff(coeff), m_i(i), m_low_bound(at_low) {}
    bool at_upper_bound() const { return !m_low_bound; }
    bool at_low_bound() const { return m_low_bound; }
};
template <typename T, typename X> 
struct implied_bound_evidence_signature {
    std::vector<bound_signature<T>> m_evidence;
    unsigned m_j; // found new bound
    bool m_low_bound;    
    X m_bound;
};
}
