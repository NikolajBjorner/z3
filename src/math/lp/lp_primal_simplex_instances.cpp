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
#include "lp_primal_simplex.cpp"
template bool lean::lp_primal_simplex<double, double>::bounds_hold(std::unordered_map<std::string, double, std::hash<std::string>, std::equal_to<std::string>, std::allocator<std::pair<std::string const, double> > > const&);
template bool lean::lp_primal_simplex<double, double>::row_constraints_hold(std::unordered_map<std::string, double, std::hash<std::string>, std::equal_to<std::string>, std::allocator<std::pair<std::string const, double> > > const&);
template double lean::lp_primal_simplex<double, double>::get_current_cost() const;
template lean::lp_primal_simplex<double, double>::~lp_primal_simplex();
template lean::lp_primal_simplex<lean::mpq, lean::mpq>::~lp_primal_simplex();
template lean::mpq lean::lp_primal_simplex<lean::mpq, lean::mpq>::get_current_cost() const;
template void lean::lp_primal_simplex<double, double>::find_maximal_solution();
template void lean::lp_primal_simplex<lean::mpq, lean::mpq>::find_maximal_solution();
