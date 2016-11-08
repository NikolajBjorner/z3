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
#include "util/lp/stacked_vector.h"
namespace lean {

template <typename T, typename X>
class lar_core_solver  {
    // m_sign_of_entering is set to 1 if the entering variable needs
    // to grow and is set to -1  otherwise
    int m_sign_of_entering_delta;
    std::vector<std::pair<mpq, unsigned>> m_infeasible_sum;
    int m_infeasible_sum_sign = 0; // todo: get rid of this field
    std::vector<X> m_right_sides_dummy;
    std::vector<T> m_costs_dummy;
public:
    std::vector<numeric_pair<mpq>> m_x; // the solution
    stacked_vector<column_type> m_column_types;
    stacked_vector<numeric_pair<mpq>> m_low_bounds;
    stacked_vector<numeric_pair<mpq>> m_upper_bounds;
    static_matrix<mpq, numeric_pair<mpq>> m_A;
    stacked_vector<unsigned> m_pushed_basis;
    std::vector<unsigned> m_basis;
    std::vector<unsigned> m_nbasis;
    std::vector<int> m_heading;
    lp_primal_core_solver<T, X> m_primal_solver;

    lar_core_solver(
                    lp_settings & settings,
                    const column_namer & column_names
                    );

    int get_infeasible_sum_sign() const { return m_infeasible_sum_sign;   }

    const std::vector<std::pair<mpq, unsigned>> & get_infeasibility_info(int & inf_sign) const {
        inf_sign = m_infeasible_sum_sign;
        return m_infeasible_sum;
    }

    column_type get_column_type(unsigned j) { return m_column_types[j];}
    
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

    unsigned m_m() const {
        return m_A.row_count();
    }

    unsigned m_n() const {
        return m_A.column_count();
    }
    
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


    const indexed_vector<T> & get_pivot_row() const {
        return m_primal_solver.m_pivot_row;
    }
    
    void fill_not_improvable_zero_sum();

    void pop_basis(unsigned k) {
        m_pushed_basis.pop(k);
        m_heading.clear();
        m_heading.resize(m_A.column_count(), -10000000);
        m_basis.clear();
        for (unsigned i = 0; i < m_pushed_basis.size(); i++ ) {
            unsigned j = m_pushed_basis[i];
            m_heading[j] = i;
            m_basis.push_back(j);
        }
        
        m_nbasis.clear();
        for (unsigned j = 0; j < m_heading.size(); j++) {
            if (m_column_types[j] == fixed) continue;
            int & pos = m_heading[j]; // we are going to change it!
            if (pos < 0 ) { // j is in nbasis
                pos = -1 - static_cast<int>(m_nbasis.size());
                m_nbasis.push_back(j);
            }
        }
    }

    void push() {
        m_A.push();
        m_column_types.push();
        m_low_bounds.push();
        m_upper_bounds.push();
        sort_and_push_basis();
    }
    
    void sort_and_push_basis() {
        lean_assert(m_pushed_basis.size() <= m_basis.size());
        for (unsigned i = 0; i < m_basis.size();i++) {
            if (i == m_pushed_basis.size()) {
                m_pushed_basis.push_back(m_basis[i]);
            } else {
                m_pushed_basis[i] = m_basis[i];
            }
        }
        m_pushed_basis.push();
    }

    void pop(unsigned k) {
        m_A.pop(k);
        m_low_bounds.pop(k);
        m_upper_bounds.pop(k);
        m_column_types.pop(k);
        if (m_primal_solver.m_factorization != nullptr) {
            delete m_primal_solver.m_factorization;
            m_primal_solver.m_factorization = nullptr;
        }
        m_x.resize(m_A.column_count());
        pop_basis(k);
        lean_assert(m_primal_solver.basis_heading_is_correct());
    }
};
}
