/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/lp_settings.h"
#include "util/lp/lar_constraints.h"
namespace lean {
    struct bound_evidence {
        std::vector<std::pair<mpq, constraint_index>> m_evidence;
        unsigned m_j; // found var
        lconstraint_kind m_kind;
        mpq m_bound;
    };
}
