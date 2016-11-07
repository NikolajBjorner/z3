/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include <vector>
#include <functional>
#include "util/lp/lar_core_solver.cpp"
template lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::lar_core_solver(
                                                                                           std::vector<unsigned int, std::allocator<unsigned int> >&,
                                                                                           std::vector<unsigned> &,
                                                                                           std::vector<int> &,
                                                                                           lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&,
                                                                                           lean::lp_settings&,
                                                                                           const column_namer&);
template void lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::solve();
template void lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::prefix();
template void lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::print_column_info(unsigned int, std::ostream & out) const;
template bool lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::is_empty() const;
template void lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::calculate_pivot_row(unsigned int);
