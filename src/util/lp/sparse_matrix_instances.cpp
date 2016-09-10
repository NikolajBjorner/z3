/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include <memory>
#include "util/lp/lp_settings.h"
#include "util/lp/lu.h"
#include "util/lp/sparse_matrix.cpp"
#include "util/lp/dense_matrix.h"
namespace lean {
template double sparse_matrix<double, double>::dot_product_with_row<double>(unsigned int, std::vector<double> const&) const;
template void sparse_matrix<double, double>::add_new_element(unsigned int, unsigned int, double);
template void sparse_matrix<double, double>::divide_row_by_constant(unsigned int, double&, lp_settings&);
template void sparse_matrix<double, double>::fill_eta_matrix(unsigned int, eta_matrix<double, double>**);
template const double & sparse_matrix<double, double>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<double, double>::get_number_of_nonzeroes() const;
template unsigned sparse_matrix<double, double>::get_number_of_nonzeroes_below_row(unsigned int) const;
template bool sparse_matrix<double, double>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned sparse_matrix<double, double>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<double, double>::pivot_row_to_row(unsigned int, double, unsigned int, lp_settings&);
template bool sparse_matrix<double, double>::pivot_with_eta(unsigned int, eta_matrix<double, double>*, lp_settings&);
template void sparse_matrix<double, double>::prepare_for_factorization();
template void sparse_matrix<double, double>::remove_element(std::vector<indexed_value<double> >&, indexed_value<double>&);
template void     sparse_matrix<double, double>::replace_column(unsigned int, indexed_vector<double>&, lp_settings&);
template void     sparse_matrix<double, double>::set(unsigned int, unsigned int, double);
template void     sparse_matrix<double, double>::set_max_in_row(std::vector<indexed_value<double> >&);
template bool sparse_matrix<double, double>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<double>&, lp_settings&);
template bool sparse_matrix<double, double>::shorten_active_matrix(unsigned int, eta_matrix<double, double>*);
template void sparse_matrix<double, double>::solve_y_U(std::vector<double>&) const;
template sparse_matrix<double, double>::sparse_matrix(static_matrix<double, double> const&, std::vector<unsigned int>&);
template sparse_matrix<double, double>::sparse_matrix(unsigned int);
template void     sparse_matrix<mpq, mpq>::add_new_element(unsigned int, unsigned int, mpq);
template void     sparse_matrix<mpq, mpq>::divide_row_by_constant(unsigned int, mpq&, lp_settings&);
template void     sparse_matrix<mpq, mpq>::fill_eta_matrix(unsigned int, eta_matrix<mpq, mpq>**);
template  mpq const & sparse_matrix<mpq, mpq>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<mpq, mpq>::get_number_of_nonzeroes() const;
template unsigned sparse_matrix<mpq, mpq>::get_number_of_nonzeroes_below_row(unsigned int) const;
template bool sparse_matrix<mpq, mpq>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned sparse_matrix<mpq, mpq>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<mpq, mpq>::pivot_with_eta(unsigned int, eta_matrix<mpq, mpq>*, lp_settings&);
template void  sparse_matrix<mpq, mpq>::prepare_for_factorization();
template void   sparse_matrix<mpq, mpq>::remove_element(std::vector<indexed_value<mpq>> &, indexed_value<mpq>&);
template void     sparse_matrix<mpq, mpq>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     sparse_matrix<mpq, mpq>::set_max_in_row(std::vector<indexed_value<mpq>>&);
template bool sparse_matrix<mpq, mpq>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool sparse_matrix<mpq, mpq>::shorten_active_matrix(unsigned int, eta_matrix<mpq, mpq>*);
template void     sparse_matrix<mpq, mpq>::solve_y_U(std::vector<mpq>&) const;
template sparse_matrix<mpq, mpq>::sparse_matrix(static_matrix<mpq, mpq> const&, std::vector<unsigned int>&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::add_new_element(unsigned int, unsigned int, mpq);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::divide_row_by_constant(unsigned int, mpq&, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::fill_eta_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >**);
template const mpq & sparse_matrix<mpq, numeric_pair<mpq>>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::get_number_of_nonzeroes() const;
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::get_number_of_nonzeroes_below_row(unsigned int) const;
template bool sparse_matrix<mpq, numeric_pair<mpq>>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<mpq, numeric_pair<mpq>>::pivot_with_eta(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::prepare_for_factorization();
template void     sparse_matrix<mpq, numeric_pair<mpq>>::remove_element(std::vector<indexed_value<mpq>>&, indexed_value<mpq>&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::set_max_in_row(std::vector<indexed_value<mpq>>&);
template bool sparse_matrix<mpq, numeric_pair<mpq>>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool     sparse_matrix<mpq, numeric_pair<mpq>>::shorten_active_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::solve_y_U(std::vector<mpq>&) const;
template sparse_matrix<mpq, numeric_pair<mpq>>::sparse_matrix(static_matrix<mpq, numeric_pair<mpq> > const&, std::vector<unsigned int>&);
template void sparse_matrix<double, double>::double_solve_U_y<double>(indexed_vector<double>&, const lp_settings  &);
template void sparse_matrix<mpq, mpq>::double_solve_U_y<mpq>(indexed_vector<mpq>&, const lp_settings&);
template void sparse_matrix<mpq, numeric_pair<mpq>>::double_solve_U_y<mpq>(indexed_vector<mpq>&, const lp_settings&);
template void sparse_matrix<mpq, numeric_pair<mpq> >::double_solve_U_y<numeric_pair<mpq> >(indexed_vector<numeric_pair<mpq>>&, const lp_settings&);
template void lean::sparse_matrix<double, double>::solve_U_y_indexed_only<double>(lean::indexed_vector<double>&, const lp_settings&);
template void lean::sparse_matrix<lean::mpq, lean::mpq>::solve_U_y_indexed_only<lean::mpq>(lean::indexed_vector<lean::mpq>&, const lp_settings &);
#ifdef LEAN_DEBUG
template bool sparse_matrix<double, double>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
template bool sparse_matrix<mpq, mpq>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
template bool sparse_matrix<mpq, numeric_pair<mpq> >::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
#endif
}
template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_U_y_indexed_only<lean::mpq>(lean::indexed_vector<lean::mpq>&, const lp_settings &);
template void lean::sparse_matrix<lean::mpq, lean::mpq>::solve_U_y<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::sparse_matrix<lean::mpq, lean::mpq>::double_solve_U_y<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::sparse_matrix<double, double>::solve_U_y<double>(std::vector<double, std::allocator<double> >&);
template void lean::sparse_matrix<double, double>::double_solve_U_y<double>(std::vector<double, std::allocator<double> >&);
template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_U_y<lean::numeric_pair<lean::mpq> >(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::double_solve_U_y<lean::numeric_pair<lean::mpq> >(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template void lean::sparse_matrix<double, double>::find_error_in_solution_U_y_indexed<double>(lean::indexed_vector<double>&, lean::indexed_vector<double>&);
template double lean::sparse_matrix<double, double>::dot_product_with_row<double>(unsigned int, lean::indexed_vector<double> const&) const;
template void lean::sparse_matrix<lean::mpq, lean::mpq>::find_error_in_solution_U_y_indexed<lean::mpq>(lean::indexed_vector<lean::mpq>&, lean::indexed_vector<lean::mpq>&);
template lean::mpq lean::sparse_matrix<lean::mpq, lean::mpq>::dot_product_with_row<lean::mpq>(unsigned int, lean::indexed_vector<lean::mpq> const&) const;
template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::find_error_in_solution_U_y_indexed<lean::mpq>(lean::indexed_vector<lean::mpq>&, lean::indexed_vector<lean::mpq>&);
template lean::mpq lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::dot_product_with_row<lean::mpq>(unsigned int, lean::indexed_vector<lean::mpq> const&) const;
template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::find_error_in_solution_U_y_indexed<lean::numeric_pair<lean::mpq> >(lean::indexed_vector<lean::numeric_pair<lean::mpq> >&, lean::indexed_vector<lean::numeric_pair<lean::mpq> >&);
template lean::numeric_pair<lean::mpq> lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::dot_product_with_row<lean::numeric_pair<lean::mpq> >(unsigned int, lean::indexed_vector<lean::numeric_pair<lean::mpq> > const&) const;
template void lean::sparse_matrix<lean::mpq, lean::mpq>::extend_and_sort_active_rows(std::vector<unsigned int, std::allocator<unsigned int> > const&, std::vector<unsigned int, std::allocator<unsigned int> >&);

template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::extend_and_sort_active_rows(std::vector<unsigned int, std::allocator<unsigned int> > const&, std::vector<unsigned int, std::allocator<unsigned int> >&);

template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_U_y<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::double_solve_U_y<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::sparse_matrix< lean::mpq,lean::numeric_pair< lean::mpq> >::set(unsigned int,unsigned int, lean::mpq);
template void lean::sparse_matrix<double, double>::solve_y_U_indexed(lean::indexed_vector<double>&, const lp_settings & );
template void lean::sparse_matrix<lean::mpq, lean::mpq>::solve_y_U_indexed(lean::indexed_vector<lean::mpq>&, const lp_settings &);
template void lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_y_U_indexed(lean::indexed_vector<lean::mpq>&, const lp_settings &);

