/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <string>
#include <vector>
#include "util/lp/lar_core_solver.h"
namespace lean {
template <typename T, typename X>
lar_core_solver<T, X>::lar_core_solver(
                                       std::vector<unsigned> & basis,
                                       std::vector<unsigned> & nbasis,
                                       std::vector<int> & heading,
                                       static_matrix<T, X> & A,
                                       lp_settings & settings,
                                       const column_namer & column_names
):
    lp_primal_core_solver<T, X>(A,
                              m_right_sides_dummy,
                              m_x,
                              basis,
                              nbasis,
                              heading,
                              m_costs_dummy,
                              m_column_types(),
                              const_cast<std::vector<numeric_pair<mpq>> &>(m_low_bounds()),
                              const_cast<std::vector<numeric_pair<mpq>> &>(m_upper_bounds()),
                              settings,
                              column_names) {}

template <typename T, typename X> void lar_core_solver<T, X>::init_costs(bool first_time) {
    lean_assert(false); // should not be called
    lean_assert(this->m_x.size() >= this->m_n());
    lean_assert(this->m_column_types.size() >= this->m_n());
    if (first_time)
        this->m_costs.resize(this->m_n());
    X inf = this->m_infeasibility;
    this->m_infeasibility = zero_of_type<X>();
    for (unsigned j = this->m_n(); j--;)
        init_cost_for_column(j);
    if (!(first_time || inf >= this->m_infeasibility)) {
        LP_OUT(this->m_settings, "iter = " << this->total_iterations() << std::endl);
        LP_OUT(this->m_settings, "inf was " << T_to_string(inf) << " and now " << T_to_string(this->m_infeasibility) << std::endl);
        lean_assert(false);
    }
    if (inf == this->m_infeasibility)
        this->m_iters_with_no_cost_growing++;
}


template <typename T, typename X> void lar_core_solver<T, X>::init_cost_for_column(unsigned j) {
    // If j is a breakpoint column, then we set the cost zero.
    // When anylyzing an entering column candidate we update the cost of the breakpoints columns to get the left or the right derivative if the infeasibility function
    const X & x = this->m_x[j];
    // set zero cost for each non-basis column
    if (this->m_basis_heading[j] < 0) {
        this->m_costs[j] = numeric_traits<T>::zero();
        return;
    }
    // j is a basis column
    switch (this->m_column_types[j]) {
    case fixed:
    case boxed:
        if (x > this->m_upper_bounds[j]) {
            this->m_costs[j] = 1;
            this->m_infeasibility += x - this->m_upper_bounds[j];
        } else if (x < this->m_low_bounds[j]) {
            this->m_infeasibility += this->m_low_bounds[j] - x;
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case low_bound:
        if (x < this->m_low_bounds[j]) {
            this->m_costs[j] = -1;
            this->m_infeasibility += this->m_low_bounds[j] - x;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case upper_bound:
        if (x > this->m_upper_bounds[j]) {
            this->m_costs[j] = 1;
            this->m_infeasibility += x - this->m_upper_bounds[j];
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
}


// returns m_sign_of_alpha_r
template <typename T, typename X>    int lar_core_solver<T, X>::column_is_out_of_bounds(unsigned j) {
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        if (this->x_below_low_bound(j)) {
            return -1;
        }
        if (this->x_above_upper_bound(j)) {
            return 1;
        }
        return 0;
    case low_bound:
        if (this->x_below_low_bound(j)) {
            return -1;
        }
        return 0;
    case upper_bound:
        if (this->x_above_upper_bound(j)) {
            return 1;
        }
        return 0;
    default:
        return 0;
        break;
    }
}



template <typename T, typename X>    void lar_core_solver<T, X>::calculate_pivot_row(unsigned i) {
    this->calculate_pivot_row_of_B_1(i);
    this->calculate_pivot_row_when_pivot_row_of_B1_is_ready();
}

template <typename T, typename X> void lar_core_solver<T, X>::print_cost(std::ostream & out) {
    out << "reduced costs " << std::endl;
    for (unsigned j = 0; j < this->m_n(); j++) {
        if (numeric_traits<T>::is_zero(this->m_d[j])) continue;
        out << T_to_string(this->m_d[j]) << this->column_name(j) << " ";
    }
    out << std::endl;
}

template <typename T, typename X> void lar_core_solver<T, X>::update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta) {
    if (entering != leaving) {
        update_basis_and_x_lar(entering, leaving, delta);       
    }
    else {
        update_x_lar(entering, delta);
    }
}


template <typename T, typename X> bool lar_core_solver<T, X>::is_done() {
    if (this->m_status == OPTIMAL) return true;
    if (this->m_status == INFEASIBLE) {
        /*        if (this->m_settings.lar_row_feasibility_only == false) {
            if (!find_evidence_row()) {
                this->m_status = FEASIBLE;
                lar_row_feasibility_only_loop();
            }
            }*/
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

template <typename T, typename X>  void lar_core_solver<T, X>::move_as_many_as_possible_fixed_columns_to_non_basis() {
    unsigned i = 0; // points to basis
    auto& bs = this->m_basis;
    unsigned j = 0; // points to m_column_types
    auto & ct = this->m_column_type;
    std::vector<int> heading(this->m_n(), -1);
    for (int i = 0; i < bs.size(); i ++) heading[bs[j]] = i;
    lean_assert(this->m_basis.size() == this->m_m());
    while (i < this->m_m() && j < ct.size()) {
        unsigned basis_j = bs[i];
        if (ct[basis_j] != fixed) {i++; continue;}
        do {
            if (heading[j] == -numeric_traits<T>::one() && ct[j] != fixed)
                break;
            j++;
        } while (j < ct.size());
        if (j == ct.size()) break;
        bs[i++] = j++;
    }
}





template <typename T, typename X> void lar_core_solver<T, X>::prefix() {
    this->m_b.resize(this->m_m());
    this->m_breakpoint_indices_queue.resize(this->m_n());
    this->m_copy_of_xB.resize(this->m_n());
    this->m_costs.resize(this->m_n());
    this->m_d.resize(this->m_n());
    this->m_ed.resize(this->m_m());
    this->m_pivot_row.resize(this->m_n());
    this->m_pivot_row_of_B_1.resize(this->m_m());
    this->m_w.resize(this->m_m());
    this->m_y.resize(this->m_m());
    this->m_steepest_edge_coefficients.resize(this->m_n());
    this->m_column_norms.clear();
    this->m_column_norms.resize(this->m_n(), one_of_type<mpq>());
    this->m_inf_set.clear();
    this->m_inf_set.resize(this->m_n());
}



template <typename T, typename X>    void lar_core_solver<T, X>::fill_evidence(unsigned row) {
    m_infeasible_sum.clear();
    m_infeasible_sum.push_back(std::make_pair(numeric_traits<T>::one(), this->m_basis[row]));
    for (unsigned j = 0; j < this->m_basis_heading.size(); j++) {
        if (this->m_basis_heading[j] >= 0) continue;
        T aj = this->m_pivot_row[j];
        if (!numeric_traits<T>::is_zero(aj)) {
            m_infeasible_sum.push_back(std::make_pair(aj, j));
        }
    }
}



template <typename T, typename X> void lar_core_solver<T, X>::fill_not_improvable_zero_sum() {
    //  reusing the existing mechanism for row_feasibility_loop
    m_infeasible_sum_sign = this->m_settings.use_breakpoints_in_feasibility_search? -1 : 1;
    m_infeasible_sum.clear();
    for (auto j : this->m_basis) {
        const T & cost_j = this->m_costs[j];
        if (!numeric_traits<T>::is_zero(cost_j)) {
            m_infeasible_sum.push_back(std::make_pair(cost_j, j));
        }
    }
    // m_costs are expressed by m_d ( additional costs), substructing the latter gives 0
    for (unsigned j = 0; j < this->m_n(); j++) {
        if (this->m_basis_heading[j] >= 0) continue;
        const T & d_j = this->m_d[j];
        if (!numeric_traits<T>::is_zero(d_j)) {
            m_infeasible_sum.push_back(std::make_pair(-d_j, j));
        }
            
    }
}


template <typename T, typename X> void lar_core_solver<T, X>::solve() {
    prefix();
    if (is_empty()) {
        this->m_status = OPTIMAL;
        return;
    }

    lean_assert(!this->A_mult_x_is_off());
    lean_assert(this->non_basis_columns_are_set_correctly());
    this->find_feasible_solution();
    if (this->m_status == INFEASIBLE) {
        fill_not_improvable_zero_sum();
    } else  {
        this->m_status = OPTIMAL;
    }
}
template <typename T, typename X> void lar_core_solver<T, X>::print_column_info(unsigned j, std::ostream & out) const {
    out << "type = " << column_type_to_string(this->m_column_types[j]) << std::endl;
    switch (this->m_column_types[j]) {
    case fixed:
    case boxed:
        out << "(" << this->m_low_bounds[j] << ", " << this->m_upper_bounds[j] << ")" << std::endl;
        break;
    case low_bound:
        out << this->m_low_bounds[j] << std::endl;
        break;
    case upper_bound:
        out << this->m_upper_bounds[j] << std::endl;
        break;
    default:
        lean_assert(false);
    }
}

}

