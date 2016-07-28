/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#ifdef LEAN_DEBUG
#include "util/lp/matrix.cpp"
#include "util/lp/static_matrix.h"
#include <string>
template void lean::print_matrix<double, double>(lean::matrix<double, double> const*, std::ostream & out);
template bool lean::matrix<double, double>::is_equal(lean::matrix<double, double> const&);
template void lean::print_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >(lean::matrix<lean::mpq, lean::numeric_pair<lean::mpq> > const *, std::basic_ostream<char, std::char_traits<char> > &);
template void lean::print_matrix<lean::mpq, lean::mpq>(lean::matrix<lean::mpq, lean::mpq> const*, std::ostream&);
template bool lean::matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::is_equal(lean::matrix<lean::mpq, lean::numeric_pair<lean::mpq> > const&);
template bool lean::matrix<lean::mpq, lean::mpq>::is_equal(lean::matrix<lean::mpq, lean::mpq> const&);
#endif
