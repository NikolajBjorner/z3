/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <string>
#include <utility>
#include "util/lp/lp_core_solver_base.h"
#include <algorithm>
#include "util/lp/indexed_vector.h"
#include "util/lp/binary_heap_priority_queue.h"
#include "util/lp/breakpoint.h"
#include "util/lp/stacked_unordered_set.h"
#include "util/lp/lp_primal_core_solver.h"
namespace lean {

template <typename T, typename X>
class lar_core_solver : public lp_primal_core_solver<T, X> {
    // m_sign_of_entering is set to 1 if the entering variable needs
    // to grow and is set to -1  otherwise
    int m_sign_of_entering_delta;
    X m_infeasibility;
    std::vector<breakpoint<X>> m_breakpoints;
    binary_heap_priority_queue<X> m_breakpoint_indices_queue;
    std::vector<std::pair<mpq, unsigned>> m_infeasible_row;
    int m_infeasible_row_sign = 0; // todo: get rid of this field
    std::vector<X> m_right_sides_dummy;
    std::vector<T> m_costs_dummy;
    std::unordered_set<unsigned> & m_columns_out_of_bounds;
public:
    lar_core_solver(std::vector<X> & x,
                    const std::vector<column_type> & column_types,
                    std::vector<X> & low_bounds,
                    std::vector<X> & upper_bounds,
                    std::vector<unsigned> & basis,
                    std::vector<unsigned> & nbasis,
                    std::vector<int> & heading,
                    static_matrix<T, X> & A,
                    lp_settings & settings,
                    const column_namer & column_names,
                    std::unordered_set<unsigned> & columns_out_of_bounds
                    );

    int get_infeasible_row_sign() const { return m_infeasible_row_sign;   }

    const std::vector<std::pair<mpq, unsigned>> & get_infeasibility_info(int & inf_sign) const {
        inf_sign = m_infeasible_row_sign;
        return m_infeasible_row;
    }

    void init_costs(bool first_time);

    void init_cost_for_column(unsigned j);

    // returns m_sign_of_alpha_r
    int column_is_out_of_bounds(unsigned j);

    bool can_enter_basis_mpq(unsigned j);


    void calculate_pivot_row(unsigned i);


    X get_deb_inf_column(unsigned j);

    X get_deb_inf();

    bool debug_profit_delta(unsigned j, const T & delta, std::ostream & out);

    bool debug_profit(unsigned j, std::ostream & out);

    int choose_column_entering_basis();

    void one_iteration();


    void decide_on_status_when_cannot_enter();
    template <typename L>
    bool same_sign_with_entering_delta(const L & a) {
        return (a > zero_of_type<L>() && m_sign_of_entering_delta > 0) || (a < zero_of_type<L>() && m_sign_of_entering_delta < 0);
    }

    // j is the basic column, x is the value at x[j]
    // d is the coefficient before m_entering in the row with j as the basis column
    void try_add_breakpoint(unsigned j, const X & x, const T & d, breakpoint_type break_type, const X & break_value);
    void add_breakpoint(unsigned j, X delta, breakpoint_type type);

    void try_add_breakpoint_in_row(unsigned i);

    std::string break_type_to_string(breakpoint_type type);

    void print_breakpoint(const breakpoint<X> * b, std::ostream & out);

    void print_bound_info_and_x(unsigned j, std::ostream & out);

    void clear_breakpoints();

    void fill_breakpoints_array(unsigned entering);

    void advance_on_entering(unsigned entering);

    void print_cost(std::ostream & out);

    void update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta);

    void advance_on_sorted_breakpoints(unsigned entering);

    void change_slope_on_breakpoint(unsigned entering, breakpoint<X> * b, T & slope_at_entering);

    bool row_is_infeasible(unsigned row);

    bool row_is_evidence(unsigned row);

    bool find_evidence_row();


    bool is_done();

    void move_as_many_as_possible_fixed_columns_to_non_basis();

    void prefix();

    bool is_tiny() const { return this->m_m() < 10 && this->m_n() < 20; }

    bool is_empty() const { return this->m_m() == 0 && this->m_n() == 0; }

    void feasibility_loop();

    unsigned get_number_of_inf_rows() const;


    void row_feasibility_loop();

    int find_infeasible_row_and_set_infeasible_row_sign();

    int get_infeasibility_sign(unsigned j) const;


    template <typename L>
    int get_sign(const L & v) {
        return v > zero_of_type<L>() ? 1 : (v < zero_of_type<L>() ? -1 : 0);
    }

    bool improves_pivot_row_inf(unsigned j, int inf_sign);

    int choose_entering_column_for_row_inf_strategy();
    int choose_entering_column_for_row_inf_strategy_randomly();
    int choose_entering_column_for_row_inf_strategy_by_min_col_norm();
    void fill_evidence(unsigned row);


    void update_delta_of_entering_and_leaving_candidates(X del, X & delta,
                                                         std::vector<unsigned> & leaving_candidates,
                                                         unsigned bj);

    void update_delta_of_entering(int delta_sign, unsigned row, X & delta,
                                  std::vector<unsigned> & leaving_candidates);

    unsigned find_leaving_for_inf_row_strategy(std::vector<unsigned> & leaving_candidates) {
        lean_assert(leaving_candidates.size() > 0);
        return leaving_candidates[my_random() % leaving_candidates.size()]; // more randomness
    }

    X find_initial_delta_and_its_sign(unsigned row, unsigned entering,
                                      int & entering_delta_sign,
                                      std::vector<unsigned> & leaving_candidates);

    void advance_on_infeasible_row_and_entering(unsigned inf_row, unsigned entering);

    void advance_on_infeasible_row(unsigned i);

    void solve();

    bool low_bounds_are_set() const { return true; }

    void print_column_info(unsigned j, std::ostream & out) const;

    void update_column_out_of_bounds(unsigned j) {
        if (this->column_is_feasible(j))
            m_columns_out_of_bounds.erase(j);
        else
            m_columns_out_of_bounds.insert(j);
    }
    
    void update_columns_out_of_bounds() {
        m_columns_out_of_bounds.clear();
        for (auto j : this->m_basis)
            update_column_out_of_bounds(j);
    }
    bool columns_out_of_bounds_are_set_correctly() const {
        for (auto j : this->m_basis) {
            if ( this->column_is_feasible(j) ==
                 (m_columns_out_of_bounds.find(j) != m_columns_out_of_bounds.end()))
                return false;
        }
        for (auto j : m_columns_out_of_bounds){ // j should be a basic column
            if (j >= this->m_basis_heading.size() || this->m_basis_heading[j] < 0)
                return false;
        }
        return true;
    }

    void update_cols_out_of_bounds() {
        for (unsigned i : this->m_ed.m_index) {
            unsigned j = this->m_basis[i];
            if (this->column_is_feasible(j))
                m_columns_out_of_bounds.erase(j);
            else
                m_columns_out_of_bounds.insert(j);
        }
    }
    
    bool update_basis_and_x_lar(int entering, int leaving, X const & tt) {
        bool ret = this->update_basis_and_x(entering, leaving, tt);
        if (ret) {
            update_cols_out_of_bounds();
            m_columns_out_of_bounds.erase(leaving);
        }
        return ret;
    }

    void update_x_lar(unsigned entering, X delta) {
        this->update_x(entering, delta);
        update_cols_out_of_bounds();
    }

    void delete_lu() {
        if (this->m_factorization != nullptr) {
            delete this->m_factorization;
            this->m_factorization = nullptr;
        }
    }
    
    int grab_first_infeasible_row_and_set_infeasible_row_sign();

    int pick_randomly_infeasible_row_and_set_infeasible_row_sign();

    int pick_min_infeasible_row_and_set_infeasible_row_sign();

    int pick_infeasible_row_with_min_norm_and_set_infeasible_row_sign();

    T get_norm_of_pivot_row(unsigned i);    
    
};
}
