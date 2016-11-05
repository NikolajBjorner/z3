/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <set>
#include <vector>
#include <string>
#include "util/lp/lp_utils.h"
#include "util/lp/core_solver_pretty_printer.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lu.h"
#include "util/lp/permutation_matrix.h"
#include "util/lp/column_namer.h"
namespace lean {

template <typename T, typename X> // X represents the type of the x variable and the bounds
class lp_core_solver_base {    
    unsigned m_total_iterations = 0;
    unsigned inc_total_iterations() { ++m_settings.st().m_total_iterations; return m_total_iterations++; }
public:
    indexed_vector<T> m_pivot_row_of_B_1;  // the pivot row of the reverse of B
    indexed_vector<T> m_pivot_row; // this is the real pivot row of the simplex tableu
    static_matrix<T, X> & m_A; // the matrix A
    std::vector<X> & m_b; // the right side
    std::vector<unsigned> & m_basis;
    std::vector<unsigned>& m_nbasis;
    std::vector<int>& m_basis_heading;
    std::vector<X> & m_x; // a feasible solution, the fist time set in the constructor
    std::vector<T> & m_costs;
    lp_settings & m_settings;
    std::vector<T> m_y; // the buffer for yB = cb
    lp_status m_status;
    // a device that is able to solve Bx=c, xB=d, and change the basis
    lu<T, X> * m_factorization;
    const column_namer & m_column_names;
    indexed_vector<T> m_w; // the vector featuring in 24.3 of the Chvatal book
    std::vector<T> m_d; // the vector of reduced costs
    indexed_vector<T> m_ed; // the solution of B*m_ed = a
    unsigned m_iters_with_no_cost_growing = 0;
    const std::vector<column_type> & m_column_types;
    std::vector<X> & m_low_bounds;
    std::vector<X> & m_upper_bounds;
    std::vector<T> m_column_norms; // the approximate squares of column norms that help choosing a profitable column
    std::vector<X> m_copy_of_xB;
    unsigned m_basis_sort_counter = 0;
    std::vector<T> m_steepest_edge_coefficients;
    unsigned m_m() const { return m_A.row_count(); } // it is the length of basis. The matrix m_A has m_m rows and the dimension of the matrix A is m_m
    unsigned m_n() const { return m_A.column_count(); } // the number of columns in the matrix m_A

    lp_core_solver_base(static_matrix<T, X> & A,
                        std::vector<X> & b, // the right side vector
                        std::vector<unsigned> & basis,
                        std::vector<unsigned> & nbasis,
                        std::vector<int> & heading,
                        std::vector<X> & x,
                        std::vector<T> & costs,
                        lp_settings & settings,
                        const column_namer& column_names,
                        const std::vector<column_type> & column_types,
                        std::vector<X> & low_bound_values,
                        std::vector<X> & upper_bound_values);

    void allocate_basis_heading();
    void init();

    virtual ~lp_core_solver_base() {
        if (m_factorization != nullptr)
            delete m_factorization;
     }

    std::vector<unsigned> & non_basis() {
        return m_nbasis;
    }

    const std::vector<unsigned> & non_basis() const { return m_nbasis; }


    
    void set_status(lp_status status) {
        m_status = status;
    }
    lp_status get_status() {
        return m_status;
    }

    void fill_cb(T * y);

    void fill_cb(std::vector<T> & y);

    void solve_yB(std::vector<T> & y);

    void solve_Bd(unsigned entering);

    void solve_Bd(unsigned entering, indexed_vector<T> & column);

    void pretty_print(std::ostream & out);

    void save_state(T * w_buffer, T * d_buffer);

    void restore_state(T * w_buffer, T * d_buffer);

    X get_cost() {
        return dot_product(m_costs, m_x);
    }

    void copy_m_w(T * buffer);

    void restore_m_w(T * buffer);

    // needed for debugging
    void copy_m_ed(T * buffer);

    void restore_m_ed(T * buffer);

    bool A_mult_x_is_off() const;

    bool A_mult_x_is_off_on_index(const std::vector<unsigned> & index) const;
    // from page 182 of Istvan Maros's book
    void calculate_pivot_row_of_B_1(unsigned pivot_row);

    void calculate_pivot_row_when_pivot_row_of_B1_is_ready();

    void update_x(unsigned entering, X delta);

    T get_var_value(unsigned j) const {
        return m_x[j];
    }

    void print_statistics(char const* str, X cost, std::ostream & message_stream);

    bool print_statistics_with_iterations_and_check_that_the_time_is_over(std::ostream & message_stream);

    bool print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const* str, std::ostream & message_stream);

    bool print_statistics_with_cost_and_check_that_the_time_is_over(X cost, std::ostream & message_stream);

    unsigned total_iterations() const { return m_total_iterations; }

    void set_total_iterations(unsigned s) { m_total_iterations = s; }

    void set_non_basic_x_to_correct_bounds();

    bool at_bound(const X &x, const X & bound) const {
        return !below_bound(x, bound) && !above_bound(x, bound);
    }

    bool below_bound(const X & x, const X & bound) const {
        if (precise<X>()) return x < bound;
        return below_bound_numeric<X>(x, bound, m_settings.primal_feasibility_tolerance);
    }

    bool above_bound(const X & x, const X & bound) const {
        if (precise<X>()) return x > bound;
        return above_bound_numeric<X>(x, bound, m_settings.primal_feasibility_tolerance);
    }

    bool x_below_low_bound(unsigned p) {
        return below_bound(m_x[p], m_low_bounds[p]);
    }

    bool x_above_low_bound(unsigned p) {
        return above_bound(m_x[p], m_low_bounds[p]);
    }

    bool x_below_upper_bound(unsigned p) {
        return below_bound(m_x[p], m_upper_bounds[p]);
    }


    bool x_above_upper_bound(unsigned p) {
        return above_bound(m_x[p], m_upper_bounds[p]);
    }
    bool x_is_at_low_bound(unsigned j) const {
        return at_bound(m_x[j], m_low_bounds[j]);
    }
    bool x_is_at_upper_bound(unsigned j) const {
        return at_bound(m_x[j], m_upper_bounds[j]);
    }

    bool x_is_at_bound(unsigned j) const {
        return x_is_at_low_bound(j) || x_is_at_upper_bound(j);
    }
    bool column_is_feasible(unsigned j) const;

    bool calc_current_x_is_feasible_include_non_basis() const;

    bool column_is_dual_feasible(unsigned j) const;

    bool d_is_not_negative(unsigned j) const;

    bool d_is_not_positive(unsigned j) const;


    bool time_is_over();

    void rs_minus_Anx(std::vector<X> & rs);

    bool find_x_by_solving();

    bool update_basis_and_x(int entering, int leaving, X const & tt);

    void init_basis_heading();

    bool basis_has_no_doubles();

    bool non_basis_has_no_doubles();

    bool basis_is_correctly_represented_in_heading();
    bool non_basis_is_correctly_represented_in_heading();

    bool basis_heading_is_correct();

    void restore_x_and_refactor(int entering, int leaving, X const & t);

    void restore_x(unsigned entering, X const & t);

    void fill_reduced_costs_from_m_y_by_rows();

    void copy_rs_to_xB(std::vector<X> & rs);
    virtual bool low_bounds_are_set() const { return false; }
    X low_bound_value(unsigned j) const { return m_low_bounds[j]; }
    X upper_bound_value(unsigned j) const { return m_upper_bounds[j]; }

    column_type get_column_type(unsigned j) const {return m_column_types[j]; }

    bool pivot_row_element_is_too_small_for_ratio_test(unsigned j) {
        return m_settings.abs_val_is_smaller_than_pivot_tolerance(m_pivot_row[j]);
    }

    X bound_span(unsigned j) const {
        return m_upper_bounds[j] - m_low_bounds[j];
    }

    std::string column_name(unsigned column) const;

    void copy_right_side(std::vector<X> & rs);

    void add_delta_to_xB(std::vector<X> & del);

    void find_error_in_BxB(std::vector<X>& rs);

    // recalculates the projection of x to B, such that Ax = b, whereab is the right side
    void solve_Ax_eq_b();

    void snap_column_to_bound(unsigned j) {
        switch (m_column_types[j]) {
        case fixed:
        case boxed:
            if (x_is_at_bound(j))
                break; // we should preserve x if possible
            m_x[j] = m_low_bounds[j];
            break;
        case low_bound:
            if (x_is_at_low_bound(j))
                break;
            m_x[j] = m_low_bounds[j];
            break;
        case upper_bound:
            if (x_is_at_upper_bound(j))
                break;
            m_x[j] = m_upper_bounds[j];
            break;
        default:
            break;
        }
    }
    void snap_non_basic_x_to_bound();
    void snap_non_basic_x_to_bound_and_free_to_zeroes();
    void snap_xN_to_bounds_and_fill_xB();

    void snap_xN_to_bounds_and_free_columns_to_zeroes();

    void init_reduced_costs_for_one_iteration();

    non_basic_column_value_position get_non_basic_column_value_position(unsigned j);

    void init_lu();
    int pivots_in_column_and_row_are_different(int entering, int leaving) const;
    void pivot_fixed_vars_from_basis();
    void init_basic_part_of_basis_heading(std::vector<unsigned> & basis, std::vector<int> & basis_heading) {
        lean_assert(basis_heading.size() >= basis.size());
        unsigned m = basis.size();
        for (unsigned i = 0; i < m; i++) {
            unsigned column = basis[i];
            basis_heading[column] = i;
        }
    }

    void init_non_basic_part_of_basis_heading(std::vector<int> & basis_heading, std::vector<unsigned> & non_basic_columns) {
        non_basic_columns.clear();
        for (int j = basis_heading.size(); j--;){
            if (basis_heading[j] < 0) {
                if (m_column_types[j] != fixed) {
                    non_basic_columns.push_back(j);
                    // the index of column j in m_nbasis is (- basis_heading[j] - 1)
                    basis_heading[j] = - static_cast<int>(non_basic_columns.size());
                } else
                    basis_heading[j] = - 100000000; // some huge negative number
            }
        }
    }
    void init_basis_heading_and_non_basic_columns_vector(std::vector<unsigned> & basis,
                                                         std::vector<int> & basis_heading,
                                                         std::vector<unsigned> & non_basic_columns) {
        init_basic_part_of_basis_heading(basis, basis_heading);
        init_non_basic_part_of_basis_heading(basis_heading, non_basic_columns);
    }

    void change_basis_unconditionally(unsigned entering, unsigned leaving) {
        lean_assert(m_basis_heading[entering] < 0);
        int place_in_non_basis = -1 - m_basis_heading[entering];
        if (static_cast<unsigned>(place_in_non_basis) >= m_nbasis.size()) {
            m_basis_heading[entering] = place_in_non_basis = m_nbasis.size();
            m_nbasis.push_back(entering);
        }
        
        int place_in_basis =  m_basis_heading[leaving];
        m_basis_heading[entering] = place_in_basis;
        m_basis[place_in_basis] = entering;
        m_basis_heading[leaving] = -place_in_non_basis - 1;
        m_nbasis[place_in_non_basis] = leaving;
    }
    
    void change_basis(unsigned entering, unsigned leaving) {
        lean_assert(m_basis_heading[entering] < 0);
#if LEAN_DEBUG
        int j = -1 - m_basis_heading[entering];
        lean_assert(m_nbasis[j] == entering);
#endif
        
        int place_in_basis =  m_basis_heading[leaving];
        int place_in_non_basis = - m_basis_heading[entering] - 1;        
        m_basis_heading[entering] = place_in_basis;
        m_basis[place_in_basis] = entering;

        if (m_column_types[leaving] != fixed) {
            m_basis_heading[leaving] = -place_in_non_basis - 1;
            m_nbasis[place_in_non_basis] = leaving;
        } else {
            unsigned last = m_nbasis.size() - 1;
            // just remove leaving from non basis
            if (place_in_non_basis != last) {
                unsigned last_j = m_nbasis[last];
                m_basis_heading[last_j] = - place_in_non_basis - 1;
                m_nbasis[place_in_non_basis] = last_j;
            }
            m_basis_heading[leaving] = -100000000; // some huge negative number
            m_nbasis.resize(last); // shrink by one and forget the fixed column
        }
    }

    void restore_basis_change(unsigned entering, unsigned leaving) {
        if (m_basis_heading[entering] < 0) {
            return; // the basis has not been changed
        }
        change_basis(leaving, entering);
    }

    bool non_basis_column_is_set_correctly(unsigned j) const {
        if (j >= this->m_n())
            return false;
        switch (this->m_column_types[j]) {
        case fixed:
        case boxed:
            if (!this->x_is_at_bound(j))
                return false;
            break;
        case low_bound:
            if (!this->x_is_at_low_bound(j))
                return false;
            break;
        case upper_bound:
            if (!this->x_is_at_upper_bound(j))
                return false;
            break;
        case free_column:
            break;
        default:
            lean_assert(false);
            break;
        }
        return true;
    }
    bool non_basis_columns_are_set_correctly() const {
        for (unsigned j : this->m_nbasis)
            if (!non_basis_column_is_set_correctly(j))
                return false;
        return true;
    }
};

}
