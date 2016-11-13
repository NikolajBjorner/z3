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
#include "util/lp/lar_solver.h"
#include "util/lp/lp_primal_core_solver.cpp"
namespace lean {
template void lp_primal_core_solver<double, double>::find_feasible_solution();
template void lean::lp_primal_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::find_feasible_solution();
template lp_primal_core_solver<double, double>::lp_primal_core_solver(static_matrix<double, double>&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, std::vector<unsigned int, std::allocator<unsigned int> >&,
                                                                      std::vector<unsigned> & nbasis,
                                                                      std::vector<int> & heading,
 std::vector<double, std::allocator<double> >&, const std::vector<column_type, std::allocator<column_type> >&, std::vector<double, std::allocator<double> >&, lp_settings&, const column_namer&);
template lp_primal_core_solver<double, double>::lp_primal_core_solver(
                                                                      static_matrix<double, double>&, std::vector<double, std::allocator<double> >&,
                                                                      std::vector<double, std::allocator<double> >&,
                                                                      std::vector<unsigned int, std::allocator<unsigned int> >&,
                                                                      std::vector<unsigned> & nbasis,
                                                                      std::vector<int> & heading,
std::vector<double, std::allocator<double> >&, const std::vector<column_type, std::allocator<column_type> >&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, lp_settings&, const column_namer&);

template unsigned lp_primal_core_solver<double, double>::solve();
template lp_primal_core_solver<mpq, mpq>::lp_primal_core_solver(static_matrix<mpq, mpq>&, std::vector<mpq, std::allocator<mpq> >&, std::vector<mpq, std::allocator<mpq> >&, std::vector<unsigned int, std::allocator<unsigned int> >&,
                                                                std::vector<unsigned> & nbasis,
                                                                std::vector<int> & heading,
                                                                std::vector<mpq, std::allocator<mpq> >&, const std::vector<column_type, std::allocator<column_type> >&, std::vector<mpq, std::allocator<mpq> >&, std::vector<mpq, std::allocator<mpq> >&, lp_settings&, const column_namer &);
template unsigned lp_primal_core_solver<mpq, mpq>::solve();
template lean::lp_primal_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::lp_primal_core_solver(lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<int, std::allocator<int> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<lean::column_type, std::allocator<lean::column_type> > const&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, lean::lp_settings&, lean::column_namer const&);
template void lean::lp_primal_core_solver<double, double>::clear_breakpoints();
}
