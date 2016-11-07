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
    std::vector<std::pair<mpq, unsigned>> m_infeasible_sum;
    int m_infeasible_sum_sign = 0; // todo: get rid of this field
    std::vector<X> m_right_sides_dummy;
    std::vector<T> m_costs_dummy;
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

    int get_infeasible_sum_sign() const { return m_infeasible_sum_sign;   }

    const std::vector<std::pair<mpq, unsigned>> & get_infeasibility_info(int & inf_sign) const {
        inf_sign = m_infeasible_sum_sign;
        return m_infeasible_sum;
    }

    void init_costs(bool first_time);

    void init_cost_for_column(unsigned j);

    // returns m_sign_of_alpha_r
    int column_is_out_of_bounds(unsigned j);

    void calculate_pivot_row(unsigned i);
    
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

    template <typename L>
    int get_sign(const L & v) {
        return v > zero_of_type<L>() ? 1 : (v < zero_of_type<L>() ? -1 : 0);
    }



    void fill_evidence(unsigned row);



    void solve();

    bool low_bounds_are_set() const { return true; }

    void print_column_info(unsigned j, std::ostream & out) const;

    void delete_lu() {
        if (this->m_factorization != nullptr) {
            delete this->m_factorization;
            this->m_factorization = nullptr;
        }
    }
    
    void fill_not_improvable_zero_sum();
    
};
}
