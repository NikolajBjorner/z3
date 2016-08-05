/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/debug.h"
#include "util/lp/lp_settings.h"
#include <unordered_map>
namespace lean {
typedef std::unordered_map<unsigned, non_basic_column_value_position> lar_solution_signature;
}
