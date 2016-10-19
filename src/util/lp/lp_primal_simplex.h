/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <unordered_map>
#include <string>
#include <algorithm>
#include "util/lp/lp_utils.h"
#include "util/lp/column_info.h"
#include "util/lp/lp_primal_core_solver.h"
#include "util/lp/lp_solver.h"

namespace lean {
template <typename T, typename X>
class lp_primal_simplex: public lp_solver<T, X> {
    lp_primal_core_solver<T, X> * m_core_solver = nullptr;
    std::vector<X> m_low_bounds;
private:
    unsigned original_rows() { return this->m_external_rows_to_core_solver_rows.size(); }

    void fill_costs_and_x_for_first_stage_solver(unsigned original_number_of_columns);

    void init_buffer(unsigned k, std::vector<T> & r);

    void refactor();

    void set_scaled_costs();
public:
    lp_primal_simplex() {}

    column_info<T> * get_or_create_column_info(unsigned column);

    void set_status(lp_status status) {
        this->m_status = status;
    }

    lp_status get_status() {
        return this->m_status;
    }

    void fill_acceptable_values_for_x();


    void set_zero_bound(bool * bound_is_set, T * bounds,  unsigned i);

    void fill_costs_and_x_for_first_stage_solver_for_row(
                                                         int row,
                                                         unsigned & slack_var,
                                                         unsigned & artificial);



    
    void set_core_solver_bounds();

    void update_time_limit_from_starting_time(int start_time) {
        this->m_settings.time_limit -= (get_millisecond_span(start_time) / 1000.);
    }

    void find_maximal_solution();

    void fill_A_x_and_basis_for_stage_one_total_inf();

    void fill_A_x_and_basis_for_stage_one_total_inf_for_row(unsigned row);

    void solve_with_total_inf();


    ~lp_primal_simplex();

    bool bounds_hold(std::unordered_map<std::string, T> const & solution);

    T get_row_value(unsigned i, std::unordered_map<std::string, T> const & solution, bool print);

    bool row_constraint_holds(unsigned i, std::unordered_map<std::string, T> const & solution, bool print);

    bool row_constraints_hold(std::unordered_map<std::string, T> const & solution);


    T * get_array_from_map(std::unordered_map<std::string, T> const & solution);

    bool solution_is_feasible(std::unordered_map<std::string, T> const & solution) {
        return bounds_hold(solution) && row_constraints_hold(solution);
    }

    virtual T get_column_value(unsigned column) const {
        return this->get_column_value_with_core_solver(column, m_core_solver);
    }

    T get_current_cost() const;

    struct iterator_on_row:linear_combination_iterator<T> {
        std::vector<row_cell<T>> & m_row;
        unsigned m_i= 0; // offset
        iterator_on_row(std::vector<row_cell<T>> & row) : m_row(row)
        {}
        bool next(T & a, unsigned & i) {
            if (m_i == m_row.size())
                return false;
            auto &c = m_row[m_i++];
            i = c.m_j;
            a = c.get_val();
            return true;
        }
        void reset() {
            m_i = 0;
        }
        linear_combination_iterator<T>* clone() {
            return new iterator_on_row(m_row);
        }
    };
    
    void tighten_low_bound(const implied_bound_evidence_signature<T, X> & ev) {
        unsigned j = ev.m_j;
        switch (this->m_column_types[j]) {
        case free_column:
            this->m_low_bounds[j] = ev.m_bound;
            this->m_column_types[j] = low_bound;
            break;
        case upper_bound:
            this->m_low_bounds[j] = ev.m_bound;
            this->m_column_types[j] = boxed;
            break;
        case fixed:
        {
#if LEAN_DEBUG
            T delta = m_low_bounds[j] - ev.m_bound;
            lean_assert(numeric_traits<T>::is_pos(delta) && this->m_settings.abs_val_is_smaller_than_primal_feasibility_tolerance(delta));
#endif
            this->m_low_bounds[j] = ev.m_bound;
            this->set_status(INFEASIBLE);
            break;
        }
        case boxed:
        case low_bound:
            {
#if LEAN_DEBUG
                T delta = m_low_bounds[j] - ev.m_bound;
                lean_assert(numeric_traits<T>::is_pos(delta) && this->m_settings.abs_val_is_smaller_than_primal_feasibility_tolerance(delta));
#endif
            this->m_low_bounds[j] = ev.m_bound;
            break;
        }
        default:
            lean_assert(false); // cannot be here
        }
    }

    void tighten_upper_bound(const implied_bound_evidence_signature<T, X> & ev) {
        unsigned j = ev.m_j;
        switch (this->m_column_types[j]) {
        case free_column:
            this->m_upper_bounds[j] = ev.m_bound;
            this->m_column_types[j] = upper_bound;
            break;
        case low_bound:
            this->m_upper_bounds[j] = ev.m_bound;
            this->m_column_types[j] = boxed;
            break;
        case fixed:
            {
#if LEAN_DEBUG
                T delta = this->m_upper_bounds[j] - ev.m_bound;
                lean_assert(numeric_traits<T>::is_pos(delta) && this->m_settings.abs_val_is_smaller_than_primal_feasibility_tolerance(delta));
#endif
            this->m_upper_bounds[j] = ev.m_bound;
            this->set_status(INFEASIBLE);
            break;
        }
        case boxed:
        case upper_bound:
            {
#if LEAN_DEBUG
            T delta = this->m_upper_bounds[j] - ev.m_bound;
            lean_assert(numeric_traits<T>::is_pos(delta) && this->m_settings.abs_val_is_smaller_than_primal_feasibility_tolerance(delta));
#endif
            this->m_upper_bounds[j] = ev.m_bound;
            break;
        }
        default:
            lean_assert(false); // cannot be here
        }

    }

    void tighten_bounds_on_evidence(implied_bound_evidence_signature<T, X> & ev) {
        if (ev.m_low_bound)
            tighten_low_bound(ev);
        else
            tighten_upper_bound(ev);
    }

    unsigned tighten_bounds_on_row(unsigned row_index) {
        iterator_on_row it(this->m_A->m_rows[row_index]);
        /*        std::cout << " row " << row_index << std::endl;
        this->print_linear_iterator(it, std::cout);
        std::cout << std::endl;
        */
        std::vector<implied_bound_evidence_signature<T, X>> evidence;
               
        bound_analyzer_on_row<T, X>::analyze_row(it, this->m_low_bounds, this->m_upper_bounds, this->m_b[row_index], this->m_column_types, evidence, false);
        for (auto & ev : evidence)
            tighten_bounds_on_evidence(ev);
        return evidence.size();
    }
    
    void tighten_bounds() {
        unsigned n = 0;
        for (unsigned i = 0 ; i < this->m_A->row_count(); i++) {
            n += tighten_bounds_on_row(i);
        }
        LP_OUT(this->m_settings, "tighthened " << n << " bounds\n");
    }
 
};
}
