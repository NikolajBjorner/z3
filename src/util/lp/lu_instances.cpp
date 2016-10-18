/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include <vector>
#include "util/lp/lu.cpp"
template double lean::dot_product<double, double>(std::vector<double, std::allocator<double> > const&, std::vector<double, std::allocator<double> > const&);
template lean::lu<double, double>::lu(lean::static_matrix<double, double> const&, std::vector<unsigned int, std::allocator<unsigned int> >&, lean::lp_settings&);
template void lean::lu<double, double>::push_matrix_to_tail(lean::tail_matrix<double, double>*);
template void lean::lu<double, double>::replace_column(double, lean::indexed_vector<double>&, unsigned);
template void lean::lu<double, double>::solve_Bd(unsigned int, lean::indexed_vector<double>&, lean::indexed_vector<double>&);
template lean::lu<double, double>::~lu();
template void lean::lu<lean::mpq, lean::mpq>::push_matrix_to_tail(lean::tail_matrix<lean::mpq, lean::mpq>*);
template void lean::lu<lean::mpq, lean::mpq>::solve_Bd(unsigned int, lean::indexed_vector<lean::mpq>&, lean::indexed_vector<lean::mpq>&);
template lean::lu<lean::mpq, lean::mpq>::~lu();
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::push_matrix_to_tail(lean::tail_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >*);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_Bd(unsigned int, lean::indexed_vector<lean::mpq>&, lean::indexed_vector<lean::mpq>&);
template lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::~lu();
template lean::mpq lean::dot_product<lean::mpq, lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> > const&, std::vector<lean::mpq, std::allocator<lean::mpq> > const&);
template void lean::init_factorization<double, double>(lean::lu<double, double>*&, lean::static_matrix<double, double>&, std::vector<unsigned int, std::allocator<unsigned int> >&, lean::lp_settings&);
template void lean::init_factorization<lean::mpq, lean::mpq>(lean::lu<lean::mpq, lean::mpq>*&, lean::static_matrix<lean::mpq, lean::mpq>&, std::vector<unsigned int, std::allocator<unsigned int> >&, lean::lp_settings&);
template void lean::init_factorization<lean::mpq, lean::numeric_pair<lean::mpq> >(lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >*&, lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, lean::lp_settings&);
#ifdef LEAN_DEBUG
template void lean::print_matrix<double, double>(lean::sparse_matrix<double, double>&, std::ostream & out);
template void lean::print_matrix<double, double>(lean::static_matrix<double, double>&, std::ostream & out);
template bool lean::lu<double, double>::is_correct(const std::vector<unsigned>& basis);
template bool lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::is_correct( std::vector<unsigned int,class std::allocator<unsigned int> > const &);
template lean::dense_matrix<double, double> lean::get_B<double, double>(lean::lu<double, double>&, const std::vector<unsigned>& basis);
#endif

template bool lean::lu<double, double>::pivot_the_row(int); // NOLINT
template lean::numeric_pair<lean::mpq> lean::dot_product<lean::mpq, lean::numeric_pair<lean::mpq> >(std::vector<lean::mpq, std::allocator<lean::mpq> > const&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > > const&);
template void lean::lu<double, double>::init_vector_w(unsigned int, lean::indexed_vector<double>&);
template void lean::lu<double, double>::solve_By(std::vector<double, std::allocator<double> >&);
template void lean::lu<double, double>::solve_By_when_y_is_ready_for_X(std::vector<double, std::allocator<double> >&);
template void lean::lu<double, double>::solve_yB_with_error_check(std::vector<double, std::allocator<double> >&, const std::vector<unsigned>& basis);
template void lean::lu<double, double>::solve_yB_with_error_check_indexed(lean::indexed_vector<double>&, std::vector<int, std::allocator<int> > const&,  const std::vector<unsigned> & basis, const lp_settings&);
template void lean::lu<lean::mpq, lean::mpq>::replace_column(lean::mpq, lean::indexed_vector<lean::mpq>&, unsigned);
template void lean::lu<lean::mpq, lean::mpq>::solve_By(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::lu<lean::mpq, lean::mpq>::solve_By_when_y_is_ready_for_X(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::lu<lean::mpq, lean::mpq>::solve_yB_with_error_check(std::vector<lean::mpq, std::allocator<lean::mpq> >&, const std::vector<unsigned>& basis);
template void lean::lu<lean::mpq, lean::mpq>::solve_yB_with_error_check_indexed(lean::indexed_vector<lean::mpq>&, std::vector< int, std::allocator< int> > const&,  const std::vector<unsigned> & basis, const lp_settings&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB_with_error_check_indexed(lean::indexed_vector<lean::mpq>&, std::vector< int, std::allocator< int> > const&,  const std::vector<unsigned> & basis, const lp_settings&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::init_vector_w(unsigned int, lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::replace_column(lean::mpq, lean::indexed_vector<lean::mpq>&, unsigned);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_Bd_faster(unsigned int, lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_By(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_By_when_y_is_ready_for_X(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB_with_error_check(std::vector<lean::mpq, std::allocator<lean::mpq> >&, const std::vector<unsigned>& basis);
template void lean::lu<lean::mpq, lean::mpq>::solve_By(lean::indexed_vector<lean::mpq>&);
template void lean::lu<double, double>::solve_By(lean::indexed_vector<double>&);
template void lean::lu<double, double>::solve_yB_indexed(lean::indexed_vector<double>&);
template void lean::lu<lean::mpq, lean::mpq>::solve_yB_indexed(lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB_indexed(lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::mpq>::solve_By_for_T_indexed_only(lean::indexed_vector<lean::mpq>&, lean::lp_settings const&);
template void lean::lu<double, double>::solve_By_for_T_indexed_only(lean::indexed_vector<double>&, lean::lp_settings const&);
