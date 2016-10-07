/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/lp_settings.h"
#include "util/lp/lar_constraints.h"
namespace lean {
struct bound_signature {
    unsigned m_i;
    bool m_at_low;
    bound_signature(unsigned i, bool at_low) :m_i(i), m_at_low(at_low) {}
    bool at_upper_bound() const { return !m_at_low; }
    bool at_low_bound() const { return m_at_low; }
};
template <typename X> 
struct implied_bound_evidence_signature {
    std::vector<bound_signature> m_evidence;
    unsigned m_j; // found new bound
    bool m_low_bound;    
    X m_bound;
};
}
