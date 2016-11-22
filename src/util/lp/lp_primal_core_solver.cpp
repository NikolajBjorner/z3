/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <list>
#include <vector>
#include <fstream>
#include <algorithm>
#include <set>
#include <string>
#include "util/lp/lp_primal_core_solver.h"
namespace lean {
// This core solver solves (Ax=b, low_bound_values \leq x \leq upper_bound_values, maximize costs*x )
// The right side b is given implicitly by x and the basis

template <typename T, typename X>
void lp_primal_core_solver<T, X>::sort_non_basis_rational() {
    lean_assert(numeric_traits<T>::precise());

    std::sort(this->m_nbasis.begin(), this->m_nbasis.end(), [this](unsigned a, unsigned b) {
            return this->m_columns_nz[a] < this->m_columns_nz[b];
    });

    m_non_basis_list.clear();
    // reinit m_basis_heading
    for (unsigned j = 0; j < this->m_nbasis.size(); j++) {
        unsigned col = this->m_nbasis[j];
        this->m_basis_heading[col] = - static_cast<int>(j) - 1;
        m_non_basis_list.push_back(col);
    }
}


template <typename T, typename X>
void lp_primal_core_solver<T, X>::sort_non_basis() {
    if (numeric_traits<T>::precise()) {
        sort_non_basis_rational();
        return;
    }
    for (unsigned j : this->m_nbasis) {
        T const & da = this->m_d[j];
        this->m_steepest_edge_coefficients[j] = da * da / this->m_column_norms[j];
    }
    std::sort(this->m_nbasis.begin(), this->m_nbasis.end(), [this](unsigned a, unsigned b) {
            return this->m_steepest_edge_coefficients[a] > this->m_steepest_edge_coefficients[b];
    });

    m_non_basis_list.clear();
    // reinit m_basis_heading
    for (unsigned j = 0; j < this->m_nbasis.size(); j++) {
        unsigned col = this->m_nbasis[j];
        this->m_basis_heading[col] = - static_cast<int>(j) - 1;
        m_non_basis_list.push_back(col);
    }
}

template <typename T, typename X>
bool lp_primal_core_solver<T, X>::column_is_benefitial_for_entering_on_breakpoints(unsigned j) const {
    bool ret;
    const T & d = this->m_d[j];
    switch (this->m_column_types[j]) {
    case low_bound:
        lean_assert(this->x_is_at_low_bound(j));
        ret = d < -m_epsilon_of_reduced_cost;
        break;
    case upper_bound:
        lean_assert(this->x_is_at_upper_bound(j));
        ret = d > m_epsilon_of_reduced_cost;
        break;
    case fixed:
        ret = false;
        break;
    case boxed:
        {
            bool low_bound = this->x_is_at_low_bound(j);
            lean_assert(low_bound || this->x_is_at_upper_bound(j));
            ret = (low_bound && d < -m_epsilon_of_reduced_cost) || ((!low_bound) && d > m_epsilon_of_reduced_cost);
        }
        break;
    case free_column:
        ret = d > m_epsilon_of_reduced_cost || d < - m_epsilon_of_reduced_cost;
        break;
    default:
        lean_unreachable();
        ret = false;
        break;
    }
    return ret;
}
template <typename T, typename X>
bool lp_primal_core_solver<T, X>::column_is_benefitial_for_entering_basis(unsigned j) const {
    if (m_using_infeas_costs && this->m_settings.use_breakpoints_in_feasibility_search)
        return column_is_benefitial_for_entering_on_breakpoints(j);
    T dj = this->m_d[j];
    switch (this->m_column_types[j]) {
    case fixed:  break;
    case free_column:
        if (dj > m_epsilon_of_reduced_cost || dj < -m_epsilon_of_reduced_cost)
            return true;
        break;
    case low_bound:
        if (dj > m_epsilon_of_reduced_cost) return true;;
        break;
    case upper_bound:
        if (dj < -m_epsilon_of_reduced_cost) return true;
        break;
    case boxed:
        if (dj > m_epsilon_of_reduced_cost) {
            if (this->m_x[j] < this->m_upper_bounds[j] - this->bound_span(j)/2)
                return true;
            break;
        } else if (dj < - m_epsilon_of_reduced_cost) {
            if (this->m_x[j] > this->m_low_bounds[j] + this->bound_span(j)/2)
                return true;
        }
        break;
    default:
        lean_unreachable();
        break;
    }
    return false;
}

template <typename T, typename X>
int lp_primal_core_solver<T, X>::choose_entering_column_presize(unsigned number_of_benefitial_columns_to_go_over) { // at this moment m_y = cB * B(-1)
    lean_assert(numeric_traits<T>::precise());
    lean_assert(number_of_benefitial_columns_to_go_over > 0);
    if (this->m_basis_sort_counter == 0) {
        sort_non_basis();
        this->m_basis_sort_counter = 20;
    }
    else {
        this->m_basis_sort_counter--;
    }
    unsigned j_nz = this->m_m() + 1; // this number is greater than the max column size
    std::list<unsigned>::iterator entering_iter = m_non_basis_list.end();
    for (auto non_basis_iter = m_non_basis_list.begin(); number_of_benefitial_columns_to_go_over && non_basis_iter != m_non_basis_list.end(); ++non_basis_iter) {
        unsigned j = *non_basis_iter;
        if (m_forbidden_enterings.find(j) != m_forbidden_enterings.end()) {
            continue;
        }
        if (!column_is_benefitial_for_entering_basis(j))
            continue;

        // if we are here then j is a candidate to enter the basis
        unsigned t = this->m_columns_nz[j];
        if (t < j_nz) {
            j_nz = t;
            entering_iter = non_basis_iter;
            if (number_of_benefitial_columns_to_go_over)
                number_of_benefitial_columns_to_go_over--;
        } else if (t == j_nz && my_random() % 2 == 0) {
            entering_iter = non_basis_iter;
        }
    }// while (number_of_benefitial_columns_to_go_over && initial_offset_in_non_basis != offset_in_nb);
    if (entering_iter == m_non_basis_list.end())
        return -1;
    unsigned entering = *entering_iter;
    m_sign_of_entering_delta = this->m_d[entering] > 0 ? 1 : -1;
    if (m_using_infeas_costs && this->m_settings.use_breakpoints_in_feasibility_search)
        m_sign_of_entering_delta = -m_sign_of_entering_delta;
    m_non_basis_list.erase(entering_iter);
    m_non_basis_list.push_back(entering);
    return entering;
}


template <typename T, typename X>
int lp_primal_core_solver<T, X>::choose_entering_column(unsigned number_of_benefitial_columns_to_go_over) { // at this moment m_y = cB * B(-1)
    if (numeric_traits<T>::precise())
        return choose_entering_column_presize(number_of_benefitial_columns_to_go_over);
    lean_assert(number_of_benefitial_columns_to_go_over > 0);
    if (this->m_basis_sort_counter == 0) {
        sort_non_basis();
        this->m_basis_sort_counter = 20;
    } else {
        this->m_basis_sort_counter--;
    }
    T steepest_edge = zero_of_type<T>();
    std::list<unsigned>::iterator entering_iter = m_non_basis_list.end();
    for (auto non_basis_iter= m_non_basis_list.begin(); number_of_benefitial_columns_to_go_over && non_basis_iter != m_non_basis_list.end(); ++non_basis_iter) {
        unsigned j = *non_basis_iter;
        if (m_forbidden_enterings.find(j) != m_forbidden_enterings.end()) {
            continue;
        }
        if (!column_is_benefitial_for_entering_basis(j))
            continue;

        // if we are here then j is a candidate to enter the basis
        T dj = this->m_d[j];
        T t = dj * dj / this->m_column_norms[j];
        if (t > steepest_edge) {
            steepest_edge = t;
            entering_iter = non_basis_iter;
            if (number_of_benefitial_columns_to_go_over)
                number_of_benefitial_columns_to_go_over--;
        }
    }// while (number_of_benefitial_columns_to_go_over && initial_offset_in_non_basis != offset_in_nb);
    if (entering_iter != m_non_basis_list.end()) {
        unsigned entering = *entering_iter;
        m_sign_of_entering_delta = this->m_d[entering] > 0? 1 : -1;
        if (m_using_infeas_costs && this->m_settings.use_breakpoints_in_feasibility_search)
            m_sign_of_entering_delta = - m_sign_of_entering_delta;
        m_non_basis_list.erase(entering_iter);
        m_non_basis_list.push_back(entering);
        return entering;
    }
    return -1;
}

template <typename T, typename X> int lp_primal_core_solver<T, X>::advance_on_sorted_breakpoints(unsigned entering, X &t) {
    T slope_at_entering = this->m_d[entering];
    breakpoint<X> * last_bp = nullptr;
    lean_assert(m_breakpoint_indices_queue.is_empty()==false);
    while (m_breakpoint_indices_queue.is_empty() == false) {
        unsigned bi = m_breakpoint_indices_queue.dequeue();
        breakpoint<X> *b = &m_breakpoints[bi];
        change_slope_on_breakpoint(entering, b, slope_at_entering);
        last_bp = b;
        if (slope_at_entering * m_sign_of_entering_delta > - m_epsilon_of_reduced_cost) { // the slope started to increase infeasibility
            break;
        } else {
            if ((numeric_traits<T>::precise() == false) || ( numeric_traits<T>::is_zero(slope_at_entering) && my_random() % 2 == 0)) {
                // it is not cost benefitial to advance the delta more, so just break to increas the randomness
                break;
            }
        }        
    }
    lean_assert (last_bp != nullptr);
    t = last_bp->m_delta;
    return last_bp->m_j;
}


template <typename T, typename X> int
lp_primal_core_solver<T, X>::find_leaving_and_t_with_breakpoints(unsigned entering, X & t){
    lean_assert(!precise<T>());
    fill_breakpoints_array(entering);
    return advance_on_sorted_breakpoints(entering, t);
}

template <typename T, typename X> bool lp_primal_core_solver<T, X>::get_harris_theta(X & theta) {
    unsigned i = this->m_m();
    bool unlimited = true;
    while (i--) {
        if (this->m_settings.abs_val_is_smaller_than_pivot_tolerance(this->m_ed[i])) continue;
        limit_theta_on_basis_column(this->m_basis[i], - this->m_ed[i] * m_sign_of_entering_delta, theta, unlimited);
        if (!unlimited && is_zero<X>(theta)) break;
    }
    return unlimited;
}


template <typename T, typename X> int lp_primal_core_solver<T, X>::
find_leaving_on_harris_theta(X const & harris_theta, X & t) {
    int leaving = -1;
    T pivot_abs_max = zero_of_type<T>();
    // we know already that there is no bound flip on entering
    // we also know that harris_theta is limited, so we will find a leaving
    zero_harris_eps();
    unsigned i = my_random() % this->m_m();
    unsigned initial_i = i;
    int column_with_non_zero_cost = -1;
    do {
        if (this->m_settings.abs_val_is_smaller_than_pivot_tolerance(this->m_ed[i])) {
            if (++i == this->m_m())
                i = 0;
            continue;
        }
        X ratio;
        unsigned j = this->m_basis[i];
        bool unlimited = true;
        limit_theta_on_basis_column(j, - this->m_ed[i] * m_sign_of_entering_delta, ratio, unlimited);
        if ((!unlimited) && ratio <= harris_theta) {
            if (!m_recalc_reduced_costs && !current_x_is_feasible()) { // when we have made several basic variables feasible we need to recalculate the costs and the reduced costs: here we are catching this case
                if (!is_zero(this->m_costs[j])) {
                    if (column_with_non_zero_cost != -1)
                        m_recalc_reduced_costs = true;
                    else
                        column_with_non_zero_cost = j;
                }
            }
            if (leaving == -1 || abs(this->m_ed[i]) > pivot_abs_max) {
                t = ratio;
                leaving = j;
                pivot_abs_max = abs(this->m_ed[i]);
            }
        }
        if (++i == this->m_m()) i = 0;
    } while ( i != initial_i);
    if (!this->precise())
        restore_harris_eps();
    return leaving;
}


template <typename T, typename X> bool lp_primal_core_solver<T, X>::try_jump_to_another_bound_on_entering(unsigned entering,
                                                                                                          const X & theta,
                                                                                                          X & t,
                                                                                                          bool & unlimited) {
    if (this->m_column_types[entering] != boxed)
        return false;

    if (m_sign_of_entering_delta > 0) {
        t = this->m_upper_bounds[entering] - this->m_x[entering];
        if (unlimited) {
            return true;
        }
        if (t <= theta){
            lean_assert(t >= zero_of_type<X>());
            return true;
        }
    } else { // m_sign_of_entering_delta == -1
        t = this->m_x[entering] - this->m_low_bounds[entering];
        if (unlimited)
            return true;
        if (t <= theta) {
            lean_assert(t >= zero_of_type<X>());
            return true;
        }
    }

    return false;
}

template <typename T, typename X> int lp_primal_core_solver<T, X>::find_leaving_and_t_precise(unsigned entering, X & t) {
    if (!current_x_is_feasible() && this->m_settings.use_breakpoints_in_feasibility_search)
        return find_leaving_and_t_with_breakpoints(entering, t);
    bool unlimited = true;
    unsigned i = my_random() % this->m_m();
    unsigned initial_i = i;
    unsigned row_min_nz = this->m_n() + 1;
    std::vector<unsigned> leaving_candidates;
    do {
        if (numeric_traits<T>::is_zero(this->m_ed[i])) {
            if (++i == this->m_m()) i = 0;
            continue;
        }
        unsigned j = this->m_basis[i];
        limit_theta_on_basis_column(j, -this->m_ed[i] * m_sign_of_entering_delta, t, unlimited);
        if (!unlimited) {
            leaving_candidates.push_back(j);
            row_min_nz = this->m_rows_nz[i];
        }
        if (++i == this->m_m()) i = 0;
    } while (unlimited && i != initial_i);
    if (unlimited) {
        if (try_jump_to_another_bound_on_entering(entering, 1, t, unlimited)) return entering; // the value of the ratio here does not matter because we have an unlimete case
        else 
            return -1;
    }

    X ratio;
    while (i != initial_i) {
        if (numeric_traits<T>::is_zero(this->m_ed[i])) {
            if (++i == this->m_m()) i = 0;
            continue;
        }
        unsigned j = this->m_basis[i];
        unlimited = true;
        limit_theta_on_basis_column(j, -this->m_ed[i] * m_sign_of_entering_delta, ratio, unlimited);
        if (unlimited) {
            if (++i == this->m_m()) i = 0;
            continue;
        }
        unsigned i_nz = this->m_rows_nz[i];
        if (ratio < t) {
            t = ratio;
            leaving_candidates.clear();
            leaving_candidates.push_back(j);
            row_min_nz = this->m_rows_nz[i];
        } else if (ratio == t && i_nz < row_min_nz) {
            leaving_candidates.clear();
            leaving_candidates.push_back(j);
            row_min_nz = this->m_rows_nz[i];
        } else if (ratio == t && i_nz == row_min_nz) {
            leaving_candidates.push_back(j);
        }
        if (++i == this->m_m()) i = 0;
    }

    ratio = t;
    unlimited = false;
    if (try_jump_to_another_bound_on_entering(entering, t, ratio, unlimited)) {
        t = ratio;
        return entering;
    }
    unsigned k = my_random() % leaving_candidates.size();
    return leaving_candidates[k];
}

template <typename T, typename X>    int lp_primal_core_solver<T, X>::find_leaving_and_t(unsigned entering, X & t) {
    if (!current_x_is_feasible() && this->m_settings.use_breakpoints_in_feasibility_search)
        return find_leaving_and_t_with_breakpoints(entering, t);
    X theta;
    bool unlimited = get_harris_theta(theta);
    lean_assert(unlimited || theta >= zero_of_type<X>());
    if (try_jump_to_another_bound_on_entering(entering, theta, t, unlimited)) return entering;
    if (unlimited)
        return -1;
    return find_leaving_on_harris_theta(theta, t);
}



// m is the multiplier. updating t in a way that holds the following
// x[j] + t * m >= m_low_bounds[j] ( if m < 0 )
// or
// x[j] + t * m <= this->m_upper_bounds[j] ( if m > 0)
template <typename T, typename X> void
lp_primal_core_solver<T, X>::get_bound_on_variable_and_update_leaving_precisely(unsigned j, std::vector<unsigned> & leavings, T m, X & t, T & abs_of_d_of_leaving) {
    if (m > 0) {
        switch(this->m_column_types[j]) { // check that j has a low bound
        case free_column:
        case upper_bound:
            return;
        default:break;
        }
        X tt = - (this->m_low_bounds[j] - this->m_x[j]) / m;
        if (numeric_traits<X>::is_neg(tt))
            tt = zero_of_type<X>();
        if (leavings.size() == 0 || tt < t || (tt == t && m > abs_of_d_of_leaving)) {
            t = tt;
            abs_of_d_of_leaving = m;
            leavings.clear();
            leavings.push_back(j);
        }
        else if (tt == t || m == abs_of_d_of_leaving) {
            leavings.push_back(j);
        }
    } else if (m < 0){
        switch (this->m_column_types[j]) { // check that j has an upper bound
        case free_column:
        case low_bound:
            return;
        default:break;
        }

        X tt = (this->m_upper_bounds[j] - this->m_x[j]) / m;
        if (numeric_traits<X>::is_neg(tt))
            tt = zero_of_type<X>();
        if (leavings.size() == 0 || tt < t || (tt == t && - m > abs_of_d_of_leaving)) {
            t = tt;
            abs_of_d_of_leaving = - m;
            leavings.clear();
            leavings.push_back(j);
        } else if (tt == t || m == abs_of_d_of_leaving) {
            leavings.push_back(j);
        }
    }
}

template <typename T, typename X>    X lp_primal_core_solver<T, X>::get_max_bound(std::vector<X> & b) {
    X ret = zero_of_type<X>();
    for (auto & v : b) {
        X a = abs(v);
        if (a > ret) ret = a;
    }
    return ret;
}

// stage1 constructor
template <typename T, typename X> lp_primal_core_solver<T, X>::lp_primal_core_solver(static_matrix<T, X> & A,
                                                                                     std::vector<X> & b, // the right side vector
                                                                                     std::vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                                                                                     std::vector<unsigned> & basis,
                                                                                     std::vector<unsigned> & nbasis,
                                                                                     std::vector<int> & heading,
                                                                                     std::vector<T> & costs,
                                                                                     const std::vector<column_type> & column_type_array,
                                                                                     std::vector<X> & low_bound_values,
                                                                                     std::vector<X> & upper_bound_values,
                                                                                     lp_settings & settings,
                                                                                     const column_namer& column_names):
lp_core_solver_base<T, X>(A, b,
                          basis,
                          nbasis,
                          heading,
                          x,
                          costs,
                          settings,
                          column_names,
                          column_type_array,
                          low_bound_values,
                          upper_bound_values),
    m_beta(A.row_count()),
    m_inf_set(A.column_count()) {
    if (!(numeric_traits<T>::precise())) {
        m_converted_harris_eps = convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance);
    } else {
        m_converted_harris_eps = zero_of_type<T>();
    }
    this->m_status = UNKNOWN;
}

// constructor
template <typename T, typename X>  lp_primal_core_solver<T, X>::
lp_primal_core_solver(static_matrix<T, X> & A,
                      std::vector<X> & b, // the right side vector
                      std::vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                      std::vector<unsigned> & basis,
                      std::vector<unsigned> & nbasis,
                      std::vector<int> & heading,
                      std::vector<T> & costs,
                      const std::vector<column_type> & column_type_array,
                      std::vector<X> & upper_bound_values,
                      lp_settings & settings,
                      const column_namer& column_names):
    lp_core_solver_base<T, X>(A, b,
                              basis,
                              nbasis,
                              heading,
                              x,
                              costs,
                              settings,
                              column_names,
                              column_type_array,
                              m_low_bounds_dummy,
                              upper_bound_values),
    m_beta(A.row_count()),
    m_converted_harris_eps(convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance)),
    m_inf_set(A.column_count()) {
    lean_assert(initial_x_is_correct());
    m_low_bounds_dummy.resize(A.column_count(), zero_of_type<T>());
    m_enter_price_eps = numeric_traits<T>::precise() ? numeric_traits<T>::zero() : T(1e-5);
#ifdef LEAN_DEBUG
    // check_correctness();
#endif
}

template <typename T, typename X> bool lp_primal_core_solver<T, X>::initial_x_is_correct() {
    std::set<unsigned> basis_set;
    for (unsigned i = 0; i < this->m_A.row_count(); i++) {
        basis_set.insert(this->m_basis[i]);
    }
    for (unsigned j = 0; j < this->m_n(); j++) {
        if (this->column_has_low_bound(j) && this->m_x[j] < numeric_traits<T>::zero()) {
            LP_OUT(this->m_settings, "low bound for variable " << j << " does not hold: this->m_x[" << j << "] = " << this->m_x[j] << " is negative " << std::endl);
            return false;
        }

        if (this->column_has_upper_bound(j) && this->m_x[j] > this->m_upper_bounds[j]) {
            LP_OUT(this->m_settings, "upper bound for " << j << " does not hold: "  << this->m_upper_bounds[j] << ">" << this->m_x[j] << std::endl);
            return false;
        }

        if (basis_set.find(j) != basis_set.end()) continue;
        if (this->m_column_types[j] == low_bound)  {
            if (numeric_traits<T>::zero() != this->m_x[j]) {
                LP_OUT(this->m_settings, "only low bound is set for " << j << " but low bound value " << numeric_traits<T>::zero() << " is not equal to " << this->m_x[j] << std::endl);
                return false;
            }
        }
        if (this->m_column_types[j] == boxed) {
            if (this->m_upper_bounds[j] != this->m_x[j] && !numeric_traits<T>::is_zero(this->m_x[j])) {
                return false;
            }
        }
    }
    return true;
}

#ifdef LEAN_DEBUG
template <typename T, typename X>   void lp_primal_core_solver<T, X>::check_Ax_equal_b() {
    dense_matrix<T, X> d(this->m_A);
    T * ls = d.apply_from_left_with_different_dims(this->m_x);
    lean_assert(vectors_are_equal<T>(ls, this->m_b, this->m_m()));
    delete [] ls;
}
template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_the_bounds() {
    for (unsigned i = 0; i < this->m_n(); i++) {
        check_bound(i);
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_bound(unsigned i) {
    lean_assert (!(this->column_has_low_bound(i) && (numeric_traits<T>::zero() > this->m_x[i])));
    lean_assert (!(this->column_has_upper_bound(i) && (this->m_upper_bounds[i] < this->m_x[i])));
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_correctness() {
    check_the_bounds();
    check_Ax_equal_b();
}
#endif

// from page 183 of Istvan Maros's book
// the basis structures have not changed yet
template <typename T, typename X>
void lp_primal_core_solver<T, X>::update_reduced_costs_from_pivot_row(unsigned entering, unsigned leaving) {
    // the basis heading has changed already
#ifdef LEAN_DEBUG
    auto & basis_heading = this->m_basis_heading;
    lean_assert(basis_heading[entering] >= 0 && static_cast<unsigned>(basis_heading[entering]) < this->m_m());
    lean_assert(basis_heading[leaving] < 0);
#endif
    T pivot = this->m_pivot_row[entering];
    T dq = this->m_d[entering]/pivot;
    for (auto j : this->m_pivot_row.m_index) {
        //            for (auto j : this->m_nbasis)
        if (this->m_basis_heading[j] >= 0) continue;
        if (j != leaving)
            this->m_d[j] -= dq * this->m_pivot_row[j];
    }
    this->m_d[leaving] = -dq;
    if (current_x_is_infeasible() && !this->m_settings.use_breakpoints_in_feasibility_search) {
        this->m_d[leaving] -= this->m_costs[leaving];
        this->m_costs[leaving] = zero_of_type<T>();
    }
    this->m_d[entering] = numeric_traits<T>::zero();
}

// return 0 if the reduced cost at entering is close enough to the refreshed
// 1 if it is way off, and 2 if it is unprofitable
template <typename T, typename X>    int lp_primal_core_solver<T, X>::refresh_reduced_cost_at_entering_and_check_that_it_is_off(unsigned entering) {
    if (numeric_traits<T>::precise()) return 0;
    T reduced_at_entering_was = this->m_d[entering];  // can benefit from going over non-zeros of m_ed
    lean_assert(abs(reduced_at_entering_was) > m_epsilon_of_reduced_cost);
    T refreshed_cost = this->m_costs[entering];
    unsigned i = this->m_m();
    while (i--) refreshed_cost -= this->m_costs[this->m_basis[i]] * this->m_ed[i];
    this->m_d[entering] = refreshed_cost;
    T delta = abs(reduced_at_entering_was - refreshed_cost);
    if (delta * 2 > abs(reduced_at_entering_was)) {
        // this->m_status = UNSTABLE;
        if (reduced_at_entering_was > m_epsilon_of_reduced_cost) {
            if (refreshed_cost <= zero_of_type<T>())
                return 2; // abort entering
        } else {
            if (refreshed_cost > -m_epsilon_of_reduced_cost)
                return 2; // abort entiring
        }
        return 1; // go on with this entering
    } else {
        if (reduced_at_entering_was > m_epsilon_of_reduced_cost) {
            if (refreshed_cost <= zero_of_type<T>())
                return 2; // abort entering
        } else {
            if (refreshed_cost > -m_epsilon_of_reduced_cost)
                return 2; // abort entiring
        }
    }
    return 0;
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::backup_and_normalize_costs() {
    if (this->m_look_for_feasible_solution_only)
        return; // no need to backup cost, since we are going to use only feasibility costs
    if (numeric_traits<T>::precise()) {
        m_costs_backup = this->m_costs;
    } else {
        T cost_max = std::max(max_abs_in_vector(this->m_costs), T(1));
        lean_assert(m_costs_backup.size() == 0);
        for (unsigned j = 0; j < this->m_costs.size(); j++)
            m_costs_backup.push_back(this->m_costs[j] /= cost_max);
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::init_run() {
    this->m_basis_sort_counter = 0; // to initiate the sort of the basis
    this->set_total_iterations(0);
    this->m_iters_with_no_cost_growing = 0;
    m_using_infeas_costs = false;
    backup_and_normalize_costs(); // todo : now always needed
    init_inf_set();
    if (current_x_is_feasible() && this->m_look_for_feasible_solution_only)
        return;
    m_epsilon_of_reduced_cost = numeric_traits<X>::precise()? zero_of_type<T>(): T(1)/T(10000000);
    m_breakpoint_indices_queue.resize(this->m_n());
    init_reduced_costs();
    if (!numeric_traits<X>::precise()) {
        this->m_column_norm_update_counter = 0;
        init_column_norms();
    } else {
        lean_assert(this->m_columns_nz.size() == this->m_n());
        lean_assert(this->m_rows_nz.size() == this->m_m());
    }
}


template <typename T, typename X>    void lp_primal_core_solver<T, X>::calc_working_vector_beta_for_column_norms(){
    lean_assert(numeric_traits<T>::precise() == false);
    lean_assert(this->m_ed.is_OK());
    lean_assert(m_beta.is_OK());
    m_beta = this->m_ed;
    this->m_factorization->solve_yB_with_error_check_indexed(m_beta, this->m_basis_heading, this->m_basis, this->m_settings);
}


template <typename T, typename X>void lp_primal_core_solver<T, X>::advance_on_entering_and_leaving(int entering, int leaving, X & t) {
    lean_assert(entering >= 0 && m_non_basis_list.back() == static_cast<unsigned>(entering));
    lean_assert(m_using_infeas_costs || t >= zero_of_type<X>());
    lean_assert(leaving >= 0 && entering >= 0);
    lean_assert(entering != leaving || !is_zero(t)); // otherwise nothing changes
    if (entering == leaving) {
        lean_assert(!this->A_mult_x_is_off() );
        this->update_x(entering, t * m_sign_of_entering_delta);
        if (this->A_mult_x_is_off_on_index(this->m_ed.m_index) && !this->find_x_by_solving()) {
            this->init_lu();
            if (!this->find_x_by_solving()) {
                this->restore_x(entering, t * m_sign_of_entering_delta);
                m_forbidden_enterings.insert(entering);
                this->m_iters_with_no_cost_growing++;
                LP_OUT(this->m_settings, "failing in advance_on_entering_and_leaving for entering == leaving = " << leaving << std::endl);
                return;
            }
        }
        if (m_using_infeas_costs) {
            lean_assert(is_zero(this->m_costs[entering])); 
            init_infeasibility_costs_for_changed_basis_only();
        }
        if (this->m_look_for_feasible_solution_only && current_x_is_feasible())
            return;
        if (need_to_switch_costs()) {
            init_reduced_costs();
        }
        this->m_iters_with_no_cost_growing = 0;
        return;
    }
    unsigned pivot_row = this->m_basis_heading[leaving];
    this->calculate_pivot_row_of_B_1(pivot_row);
    this->calculate_pivot_row_when_pivot_row_of_B1_is_ready(pivot_row);

    int pivot_compare_result = this->pivots_in_column_and_row_are_different(entering, leaving);
    if (!pivot_compare_result){;}
    else if (pivot_compare_result == 2) { // the sign is changed, cannot continue
        m_forbidden_enterings.insert(entering);
        this->m_status = UNSTABLE;
        this->m_iters_with_no_cost_growing++;
        return;
    } else {
        lean_assert(pivot_compare_result == 1);
        this->init_lu();
    }
    if (!numeric_traits<T>::precise())
        calc_working_vector_beta_for_column_norms();
    if (current_x_is_feasible() || !this->m_settings.use_breakpoints_in_feasibility_search) {
        if (m_sign_of_entering_delta == -1)
            t = -t;
    }
    if (!this->update_basis_and_x(entering, leaving, t)) {
        std::cout << "failed here\n";
        if (this->m_status == FLOATING_POINT_ERROR)
            return;
        if (this->m_look_for_feasible_solution_only) {
            this->m_status = FLOATING_POINT_ERROR;
            return;
        }
        init_reduced_costs();
        m_forbidden_enterings.insert(entering);
        return;
    }

    if (!is_zero(t)) {
        this->m_iters_with_no_cost_growing = 0;
    }
    init_infeasibility_after_update_x_if_inf(leaving);
    if (this->m_look_for_feasible_solution_only && current_x_is_feasible())
        return;
    if (numeric_traits<X>::precise() == false)
        update_or_init_column_norms(entering, leaving);

    if (need_to_switch_costs() || m_recalc_reduced_costs || m_using_infeas_costs) {
        init_reduced_costs();
    }  else {
        update_reduced_costs_from_pivot_row(entering, leaving);
    }
    lean_assert(!need_to_switch_costs());
    m_forbidden_enterings.clear();
    std::list<unsigned>::iterator it = m_non_basis_list.end();
    it--;
    * it = static_cast<unsigned>(leaving);
}
template <typename T, typename X> void lp_primal_core_solver<T, X>::advance_on_entering_precise(int entering) {
    lean_assert(numeric_traits<T>::precise());
    lean_assert(entering > -1);
    this->solve_Bd(entering);
    X t;
    int leaving = find_leaving_and_t_precise(entering, t);
    if (leaving == -1) {
        lean_assert(current_x_is_feasible());
            // we cannot have unbounded with inf costs

            this->m_status = UNBOUNDED;
            return;
        
    }
    advance_on_entering_and_leaving(entering, leaving, t);
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::advance_on_entering(int entering) {
    if (numeric_traits<T>::precise()) {
        advance_on_entering_precise(entering);
        return;
    }
    lean_assert(entering > -1);
    this->solve_Bd(entering);
    int refresh_result = refresh_reduced_cost_at_entering_and_check_that_it_is_off(entering);
    if (refresh_result) {
        this->init_lu();
        init_reduced_costs();
        if (refresh_result == 2) {
            this->m_iters_with_no_cost_growing++;
            return;
        }
    }
    X t;
    int leaving = find_leaving_and_t(entering, t);
    if (leaving == -1){
        if (!current_x_is_feasible()) {
            lean_assert(!numeric_traits<T>::precise()); // we cannot have unbounded with inf costs
               
            // if (m_look_for_feasible_solution_only) {
            //     this->m_status = INFEASIBLE;
            //     return;
            //  }
            
                
            if (this->m_status == UNSTABLE) {
                this->m_status = FLOATING_POINT_ERROR;
                return;
            }
            init_infeasibility_costs();
            this->m_status = UNSTABLE;

            return;
        }
        if (this->m_status == TENTATIVE_UNBOUNDED) {
            this->m_status = UNBOUNDED;
        } else {
            this->m_status = TENTATIVE_UNBOUNDED;
        }
        return;
    }
    advance_on_entering_and_leaving(entering, leaving, t);
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::push_forward_offset_in_non_basis(unsigned & offset_in_nb) {
    if (++offset_in_nb == this->m_nbasis.size())
        offset_in_nb = 0;
}

template <typename T, typename X>  unsigned lp_primal_core_solver<T, X>::get_number_of_non_basic_column_to_try_for_enter() {
    unsigned ret = static_cast<unsigned>(this->m_nbasis.size());
    if (this->m_status == TENTATIVE_UNBOUNDED)
        return ret; // we really need to find entering with a large reduced cost
    if (ret > 300) {
        ret = (unsigned)(ret * this->m_settings.percent_of_entering_to_check / 100);
    }
    if (ret == 0) {
        return 0;
    }
    return std::max(static_cast<unsigned>(my_random() % ret), 1u);
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::print_column_norms(std::ostream & out) {
    out << " column norms " << std::endl;
    for (unsigned j = 0; j < this->m_n(); j++) {
        out << this->m_column_norms[j] << " ";
    }
    out << std::endl;
    out << std::endl;
}

// returns the number of iterations
template <typename T, typename X> unsigned lp_primal_core_solver<T, X>::solve() {
    init_run();
    if (current_x_is_feasible() && this->m_look_for_feasible_solution_only) {
        this->m_status = FEASIBLE;
        return 0;
    }
        
    if ((!numeric_traits<T>::precise()) && this->A_mult_x_is_off()) {
        this->m_status = FLOATING_POINT_ERROR;
        return 0;
    }
    do {
        if (this->print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over((m_using_infeas_costs? "inf" : "feas"), * this->m_settings.get_message_ostream())) {
            return this->total_iterations();
        }
        one_iteration();
        switch (this->m_status) {
        case OPTIMAL:  // double check that we are at optimum
        case INFEASIBLE:
            if (numeric_traits<T>::precise())
                break;
            m_forbidden_enterings.clear();
            this->init_lu();
            lean_assert(this->m_factorization->get_status() == LU_status::OK);
            init_reduced_costs();
            if (choose_entering_column(1) == -1) {
                decide_on_status_when_cannot_find_entering();
                break;
            }
            this->m_status = UNKNOWN;
            break;
        case TENTATIVE_UNBOUNDED:
            m_forbidden_enterings.clear();
            this->init_lu();
            lean_assert(this->m_factorization->get_status() == LU_status::OK);
            init_reduced_costs();
            break;
        case UNBOUNDED:
            break;

        case UNSTABLE:
            lean_assert(! (numeric_traits<T>::precise()));
            this->init_lu();
            init_reduced_costs();
            break;

        default:
            break; // do nothing
        }
    } while (this->m_status != FLOATING_POINT_ERROR && this->m_status != UNBOUNDED
             &&
             this->m_status != OPTIMAL
             &&
             this->m_status != INFEASIBLE
             &&
             this->m_iters_with_no_cost_growing <= this->m_settings.max_number_of_iterations_with_no_improvements
             &&
             this->total_iterations() <= this->m_settings.max_total_number_of_iterations
             &&
             !(current_x_is_feasible() && this->m_look_for_feasible_solution_only));

    lean_assert(current_x_is_feasible() == false || this->calc_current_x_is_feasible_include_non_basis());
    return this->total_iterations();
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::delete_factorization() {
    if (this->m_factorization != nullptr) {
        delete this->m_factorization;
        this->m_factorization = nullptr;
    }
}

// according to Swietanowski, " A new steepest edge approximation for the simplex method for linear programming"
template <typename T, typename X> void lp_primal_core_solver<T, X>::init_column_norms() {
    lean_assert(numeric_traits<T>::precise() == false);
    for (unsigned j = 0; j < this->m_n(); j++) {
        this->m_column_norms[j] = T(static_cast<int>(this->m_A.m_columns[j].size() + 1)) 
            
            + T(static_cast<int>(my_random() % 10000)) / T(100000);
    }
}

// debug only
template <typename T, typename X> T lp_primal_core_solver<T, X>::calculate_column_norm_exactly(unsigned j) {
    lean_assert(numeric_traits<T>::precise() == false);
    indexed_vector<T> w(this->m_m());
    this->m_A.copy_column_to_vector(j, w);
    std::vector<T> d(this->m_m());
    this->m_factorization->solve_Bd_when_w_is_ready(d, w);
    T ret = zero_of_type<T>();
    for (auto v : d)
        ret += v*v;
    return ret+1;
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::update_or_init_column_norms(unsigned entering, unsigned leaving) {
    lean_assert(numeric_traits<T>::precise() == false);
    lean_assert(m_column_norm_update_counter <= this->m_settings.column_norms_update_frequency);
    if (m_column_norm_update_counter == this->m_settings.column_norms_update_frequency) {
        m_column_norm_update_counter = 0;
        init_column_norms();
    } else {
        m_column_norm_update_counter++;
        update_column_norms(entering, leaving);
    }
}

// following Swietanowski - A new steepest ...
template <typename T, typename X>    void lp_primal_core_solver<T, X>::update_column_norms(unsigned entering, unsigned leaving) {
    lean_assert(numeric_traits<T>::precise() == false);
    T pivot = this->m_pivot_row[entering];
    T g_ent = calculate_norm_of_entering_exactly() / pivot / pivot;
    if (!numeric_traits<T>::precise()) {
        if (g_ent < T(0.000001))
            g_ent = T(0.000001);
    }
    this->m_column_norms[leaving] = g_ent;

    for (unsigned j : this->m_pivot_row.m_index) {
        if (j == leaving)
            continue;
        const T & t = this->m_pivot_row[j];
        T s = this->m_A.dot_product_with_column(m_beta.m_data, j);
        T k = -2 / pivot;
        T tp = t/pivot;
        if (this->m_column_types[j] != fixed) { // a fixed columns do not enter the basis, we don't use the norm of a fixed column
            this->m_column_norms[j] = std::max(this->m_column_norms[j] + t * (t * g_ent + k * s), // see Istvan Maros, page 196
                                               1 + tp * tp);
             }
    }
}

template <typename T, typename X>    T lp_primal_core_solver<T, X>::calculate_norm_of_entering_exactly() {
    T r = numeric_traits<T>::one();
    for (auto i : this->m_ed.m_index) {
        T t = this->m_ed[i];
        r += t * t;
    }
    return r;
}

// calling it stage1 is too cryptic
template <typename T, typename X>    void lp_primal_core_solver<T, X>::find_feasible_solution() {
    this->m_look_for_feasible_solution_only = true;
    lean_assert(this->non_basis_columns_are_set_correctly());
    this->m_status = UNKNOWN;
    solve();
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::one_iteration() {
    unsigned number_of_benefitial_columns_to_go_over = get_number_of_non_basic_column_to_try_for_enter();
    int entering = choose_entering_column(number_of_benefitial_columns_to_go_over);
    if (entering == -1) {
        decide_on_status_when_cannot_find_entering();
    }
    else
        advance_on_entering(entering);
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta) {
    if (entering != leaving)
        this->update_basis_and_x(entering, leaving, delta);
    else
        this->update_x(entering, delta);
}


template <typename T, typename X> void lp_primal_core_solver<T, X>::clear_breakpoints() {
    m_breakpoints.clear();
    m_breakpoint_indices_queue.clear();
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::fill_breakpoints_array(unsigned entering) {
    clear_breakpoints();
    for (unsigned i : this->m_ed.m_index)
        try_add_breakpoint_in_row(i);

    if (this->m_column_types[entering] == boxed) {
        if (m_sign_of_entering_delta < 0)
            add_breakpoint(entering, - this->bound_span(entering), low_break);
        else
            add_breakpoint(entering, this->bound_span(entering), upper_break);
    }
}



template <typename T, typename X> bool lp_primal_core_solver<T, X>::done() {
    if (this->m_status == OPTIMAL ||this->m_status == FLOATING_POINT_ERROR) return true;
    if (this->m_status == INFEASIBLE) {
        return true;
    }
    if (this->m_iters_with_no_cost_growing >= this->m_settings.max_number_of_iterations_with_no_improvements) {
        this->m_status = ITERATIONS_EXHAUSTED; return true;
    }
    if (this->total_iterations() >= this->m_settings.max_total_number_of_iterations) {
        this->m_status = ITERATIONS_EXHAUSTED; return true;
    }
    return false;
}

template <typename T, typename X>
void lp_primal_core_solver<T, X>::init_infeasibility_costs_for_changed_basis_only() {
    for (unsigned i :  this->m_ed.m_index)
        init_infeasibility_cost_for_column(this->m_basis[i]);
    m_using_infeas_costs = true;
}


template <typename T, typename X>
void lp_primal_core_solver<T, X>::init_infeasibility_costs() {
    lean_assert(this->m_x.size() >= this->m_n());
    lean_assert(this->m_column_types.size() >= this->m_n());
    for (unsigned j = this->m_n(); j--;)
        init_infeasibility_cost_for_column(j);
    m_using_infeas_costs = true;
}

template <typename T, typename X> void
lp_primal_core_solver<T, X>::init_infeasibility_cost_for_column(unsigned j) {
    // the cost will be m_infeasibility, and we will minimize m_infeasibility
    // If j is a breakpoint column, then we set the cost zero.
    // When anylyzing an entering column candidate we update the cost of the breakpoints columns to get the left or the right derivative if the infeasibility function
    // set zero cost for each non-basis column
    if (this->m_basis_heading[j] < 0) {
        this->m_costs[j] = numeric_traits<T>::zero();
        m_inf_set.erase(j);
        return;
    }
    // j is a basis column
    switch (this->m_column_types[j]) {
    case fixed:
    case boxed:
        if (this->x_above_upper_bound(j)) {
            this->m_costs[j] = 1;
        } else if (this->x_below_low_bound(j)) {
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case low_bound:
        if (this->x_below_low_bound(j)) {
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case upper_bound:
        if (this->x_above_upper_bound(j)) {
            this->m_costs[j] = 1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case free_column:
        this->m_costs[j] = numeric_traits<T>::zero();
        break;
    default:
        lean_assert(false);
        break;
    }
    
    if (numeric_traits<T>::is_zero(this->m_costs[j])) {
        m_inf_set.erase(j);
    } else {
        m_inf_set.insert(j);
    }
    if (!this->m_settings.use_breakpoints_in_feasibility_search) {
        this->m_costs[j] = - this->m_costs[j];
    }
}


template <typename T, typename X> void lp_primal_core_solver<T, X>::print_column(unsigned j, std::ostream & out) {
    out << this->column_name(j) << " " <<   j << " " << column_type_to_string(this->m_column_type[j]) << " x = " << this->m_x[j] << " " << "c = " << this->m_costs[j];;
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        out <<  "( " << this->m_low_bounds[j] << " " << this->m_x[j] << " " << this->m_upper_bounds[j] << ")" << std::endl;
        break;
    case upper_bound:
        out <<  "( _"  << this->m_x[j] << " " << this->m_upper_bounds[j] << ")" << std::endl;
        break;
    case low_bound:
        out <<  "( " << this->m_low_bounds[j] << " " << this->m_x[j] << " " << "_ )" << std::endl;
        break;
    case free_column:
        out << "( _" << this->m_x[j] << "_)" << std::endl;
    default:
        lean_unreachable();
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::add_breakpoint(unsigned j, X delta, breakpoint_type type) {
    m_breakpoints.push_back(breakpoint<X>(j, delta, type));
    m_breakpoint_indices_queue.enqueue(m_breakpoint_indices_queue.size(), abs(delta));
}

// j is the basic column, x is the value at x[j]
// d is the coefficient before m_entering in the row with j as the basis column
template <typename T, typename X>    void lp_primal_core_solver<T, X>::try_add_breakpoint(unsigned j, const X & x, const T & d, breakpoint_type break_type, const X & break_value) {
    X diff = x - break_value;
    if (is_zero(diff)) {
        switch (break_type) {
        case low_break:
            if (!same_sign_with_entering_delta(d))
                return; // no breakpoint
            break;
        case upper_break:
            if (same_sign_with_entering_delta(d))
                return; // no breakpoint
            break;
        default: break;
        }
        add_breakpoint(j, zero_of_type<X>(), break_type);
        return;
    }
    auto delta_j =  diff / d;
    if (same_sign_with_entering_delta(delta_j))
        add_breakpoint(j, delta_j, break_type);
}

template <typename T, typename X> std::string lp_primal_core_solver<T, X>::break_type_to_string(breakpoint_type type) {
    switch (type){
    case low_break: return "low_break";
    case upper_break: return "upper_break";
    case fixed_break: return "fixed_break";
    default:
        lean_assert(false);
        break;
    }
    return "type is not found";
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::print_breakpoint(const breakpoint<X> * b, std::ostream & out) {
    out << "(" << this->column_name(b->m_j) << "," << break_type_to_string(b->m_type) << "," << T_to_string(b->m_delta) << ")" << std::endl;
    print_bound_info_and_x(b->m_j, out);
}

template <typename T, typename X>
void lp_primal_core_solver<T, X>::init_reduced_costs() {
    if (current_x_is_infeasible() && !m_using_infeas_costs) {
        init_infeasibility_costs();
    } else if (current_x_is_feasible() && m_using_infeas_costs) {
        lean_assert(m_costs_backup.size() == this->m_costs.size());
        this->m_costs = m_costs_backup;
        m_using_infeas_costs = false;
    }
    this->init_reduced_costs_for_one_iteration();
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::change_slope_on_breakpoint(unsigned entering, breakpoint<X> * b, T & slope_at_entering) {
    if (b->m_j == entering) {
        lean_assert(b->m_type != fixed_break && (!is_zero(b->m_delta)));
        slope_at_entering += m_sign_of_entering_delta;
        return;
    }

    lean_assert(this->m_basis_heading[b->m_j] >= 0);
    unsigned i_row = this->m_basis_heading[b->m_j];
    const T & d = - this->m_ed[i_row];
    if (numeric_traits<T>::is_zero(d)) return;

    T delta = m_sign_of_entering_delta * abs(d);
    switch (b->m_type) {
    case fixed_break:
        if (is_zero(b->m_delta)) {
            slope_at_entering += delta;
        } else {
            slope_at_entering += 2 * delta;
        }
        break;
    case low_break:
    case upper_break:
        slope_at_entering += delta;
        break;
    default:
        lean_assert(false);
    }
}


template <typename T, typename X>    void lp_primal_core_solver<T, X>::try_add_breakpoint_in_row(unsigned i) {
    lean_assert(i < this->m_m());
    const T & d = this->m_ed[i]; // the coefficient before m_entering in the i-th row
    if (d == 0) return; // the change of x[m_entering] will not change the corresponding basis x
    unsigned j = this->m_basis[i];
    const X & x = this->m_x[j];
    switch (this->m_column_types[j]) {
    case fixed:
        try_add_breakpoint(j, x, d, fixed_break, this->m_low_bounds[j]);
        break;
    case boxed:
        try_add_breakpoint(j, x, d, low_break, this->m_low_bounds[j]);
        try_add_breakpoint(j, x, d, upper_break, this->m_upper_bounds[j]);
        break;
    case low_bound:
        try_add_breakpoint(j, x, d, low_break, this->m_low_bounds[j]);
        break;
    case upper_bound:
        try_add_breakpoint(j, x, d, upper_break, this->m_upper_bounds[j]);
        break;
    case free_column:
        break;
    default:
        lean_assert(false);
        break;
    }
}
template <typename T, typename X> void lp_primal_core_solver<T, X>::print_bound_info_and_x(unsigned j, std::ostream & out) {
    out << "type of " << this->column_name(j) << " is " << column_type_to_string(this->m_column_types[j]) << std::endl;
    out << "x[" << this->column_name(j) << "] = " << this->m_x[j] << std::endl;
    switch (this->m_column_types[j]) {
    case fixed:
    case boxed:
        out << "[" << this->m_low_bounds[j] << "," << this->m_upper_bounds[j] << "]" << std::endl;
        break;
    case low_bound:
        out << "[" << this->m_low_bounds[j] << ", inf" << std::endl;
        break;
    case upper_bound:
        out << "inf ," << this->m_upper_bounds[j] << "]" << std::endl;
        break;
    case free_column:
        out << "inf, inf" << std::endl;
        break;
    default:
        lean_assert(false);
        break;
    }
}

}
