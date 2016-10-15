/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <string>
#include <unordered_map>
#include <algorithm>
#include <vector>
#include "util/lp/lp_settings.h"
#include "util/lp/column_info.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lp_core_solver_base.h"
#include "util/lp/scaler.h"
#include "util/lp/linear_combination_iterator.h"
#include "util/lp/bound_analyzer_on_row.h"
namespace lean {
enum lp_relation  {
    Less_or_equal,
    Equal,
    Greater_or_equal
};

template <typename T, typename X>
struct lp_constraint {
    X m_rs; // right side of the constraint
    lp_relation m_relation;
    lp_constraint() {} // empty constructor
    lp_constraint(T rs, lp_relation relation): m_rs(rs), m_relation(relation) {}
};

template <typename T, typename X>
struct linear_combination_iterator_on_vector : linear_combination_iterator<T> {
    std::vector<std::pair<T, unsigned>> & m_vector;
    int m_offset = 0;
    bool next(T & a, unsigned & i) {
        if(m_offset >= m_vector.size())
            return false;
        auto & p = m_vector[m_offset];
        a = p.first;
        i = p.second;
        m_offset++;
        return true;
    }
    void reset() {m_offset = 0;}
    linear_combination_iterator<T> * clone() {
        return new linear_combination_iterator_on_vector(m_vector);
    }
    linear_combination_iterator_on_vector(std::vector<std::pair<T, unsigned>> & vec): m_vector(vec) {}
};


template <typename T, typename X>
class lp_solver : public column_namer {
    column_info<T> * get_or_create_column_info(unsigned column);

protected:
    T get_column_cost_value(unsigned j, column_info<T> * ci) const;
public:
    unsigned m_total_iterations;
    static_matrix<T, X>* m_A = nullptr; // this is the matrix of constraints
    std::vector<T> m_b; // the right side vector
    unsigned m_first_stage_iterations = 0;
    unsigned m_second_stage_iterations = 0;
    std::unordered_map<unsigned, lp_constraint<T, X>> m_constraints;
    std::unordered_map<var_index, column_info<T>*> m_map_from_var_index_to_column_info;
    std::unordered_map<unsigned, std::unordered_map<unsigned, T> > m_A_values;
    std::unordered_map<std::string, unsigned> m_names_to_columns; // don't have to use it
    std::unordered_map<unsigned, unsigned> m_external_rows_to_core_solver_rows;
    std::unordered_map<unsigned, unsigned> m_core_solver_rows_to_external_rows;
    std::unordered_map<unsigned, unsigned> m_core_solver_columns_to_external_columns;
    std::vector<T> m_column_scale;
    std::unordered_map<unsigned, std::string>  m_name_map;
    unsigned m_artificials = 0;
    unsigned m_slacks = 0;
    std::vector<column_type> m_column_types;
    std::vector<T> m_costs;
    std::vector<T> m_x;
    std::vector<T> m_upper_bounds;
    std::vector<unsigned> m_basis;
    std::vector<unsigned> m_nbasis;
    std::vector<int> m_heading;


    lp_status m_status = lp_status::UNKNOWN;

    lp_settings m_settings;
    lp_solver() {}

    unsigned row_count() const { return this->m_A->row_count(); }

    void add_constraint(lp_relation relation, T  right_side, unsigned row_index);

    void set_cost_for_column(unsigned column, T  column_cost) {
        get_or_create_column_info(column)->set_cost(column_cost);
    }
    std::string get_column_name(unsigned j) const override;

    void set_row_column_coefficient(unsigned row, unsigned column, T const & val) {
        m_A_values[row][column] = val;
    }
    // returns the current cost
    virtual T get_current_cost() const = 0;
       // do not have to call it
    void give_symbolic_name_to_column(std::string name, unsigned column);

    virtual T get_column_value(unsigned column) const = 0;

    T get_column_value_by_name(std::string name) const;

    // returns -1 if not found
    virtual int get_column_index_by_name(std::string name) const;

    void set_low_bound(unsigned i, T bound) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_low_bound(bound);
    }

    void set_upper_bound(unsigned i, T bound) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_upper_bound(bound);
    }

    void unset_low_bound(unsigned i) {
        get_or_create_column_info(i)->unset_low_bound();
    }

    void unset_upper_bound(unsigned i) {
        get_or_create_column_info(i)->unset_upper_bound();
    }

    void set_fixed_value(unsigned i, T val) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_fixed_value(val);
    }

    void unset_fixed_value(unsigned i) {
        get_or_create_column_info(i)->unset_fixed();
    }

    lp_status get_status() const {
        return m_status;
    }

    void set_status(lp_status st)  {
        m_status = st;
    }

    
    virtual ~lp_solver();

    void flip_costs();

    virtual void find_maximal_solution() = 0;
    void set_time_limit(unsigned time_limit_in_seconds) {
        m_settings.time_limit = time_limit_in_seconds;
    }

    void set_max_iterations_per_stage(unsigned max_iterations) {
        m_settings.max_total_number_of_iterations = max_iterations;
    }

    unsigned get_max_iterations_per_stage() const {
        return m_settings.max_total_number_of_iterations;
    }
protected:
    bool problem_is_empty();

    void scale();


    void print_rows_scale_stats(std::ostream & out);

    void print_columns_scale_stats(std::ostream & out);

    void print_row_scale_stats(unsigned i, std::ostream & out);

    void print_column_scale_stats(unsigned j, std::ostream & out);

    void print_scale_stats(std::ostream & out);

    void get_max_abs_in_row(std::unordered_map<unsigned, T> & row_map);

    void pin_vars_down_on_row(std::unordered_map<unsigned, T> & row) {
        pin_vars_on_row_with_sign(row, - numeric_traits<T>::one());
    }

    void pin_vars_up_on_row(std::unordered_map<unsigned, T> & row) {
        pin_vars_on_row_with_sign(row, numeric_traits<T>::one());
    }

    void pin_vars_on_row_with_sign(std::unordered_map<unsigned, T> & row, T sign );

    bool get_minimal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound);

    bool get_maximal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound);

    bool row_is_zero(std::unordered_map<unsigned, T> & row);

    bool row_e_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index);

    bool row_ge_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index);

    bool row_le_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index);

    // analyse possible max and min values that are derived from var boundaries
    // Let us say that the we have a "ge" constraint, and the min value is equal to the rs.
    // Then we know what values of the variables are. For each positive coeff of the row it has to be
    // the low boundary of the var and for a negative - the upper.

    // this routing also pins the variables to the boundaries
    bool row_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index );

    void remove_fixed_or_zero_columns();

    void remove_fixed_or_zero_columns_from_row(unsigned i, std::unordered_map<unsigned, T> & row);

    unsigned try_to_remove_some_rows();

    void cleanup();

    void map_external_rows_to_core_solver_rows();

    void map_external_columns_to_core_solver_columns();

    unsigned number_of_core_structurals() {
        return static_cast<unsigned>(m_core_solver_columns_to_external_columns.size());
    }

    void restore_column_scales_to_one() {
        for (unsigned i = 0; i < m_column_scale.size(); i++) m_column_scale[i] = numeric_traits<T>::one();
    }

    void unscale();

    void fill_A_from_A_values();

    void fill_matrix_A_and_init_right_side();

    void count_slacks_and_artificials();

    void count_slacks_and_artificials_for_row(unsigned i);

    T low_bound_shift_for_row(unsigned i);

    void fill_m_b();

    T get_column_value_with_core_solver(unsigned column, lp_core_solver_base<T, X> * core_solver) const;
    void set_scaled_cost(unsigned j);
    void print_statistics_on_A()  {
        std::cout << "extended A[" << this->m_A->row_count() << "," << this->m_A->column_count() << "]" << std::endl;
    }

    struct row_tighten_stats {
        unsigned n_of_new_bounds = 0;
        unsigned n_of_fixed = 0;
        bool is_obsolete = false;
    };
    
    void flatten_row_with_allocated_vectors(
                                            std::unordered_map<unsigned, T> & row,
                                            std::vector<column_type> & col_types,
                                            std::vector<X> & low_bounds,
                                            std::vector<X> & upper_bounds,
                                            std::unordered_map<unsigned, unsigned> & from_flat_arrays_to_orig,
                                            std::vector<std::pair<T, unsigned>> & vector) {
        unsigned i = 0;
        for (auto &t : row) {
            T & a = t.second;
            unsigned j = t.first;
            vector.emplace_back(a, i);
            from_flat_arrays_to_orig[i] = j;
            auto it =  m_map_from_var_index_to_column_info.find(j);
            lean_assert(it != m_map_from_var_index_to_column_info.end());
            column_info<X> *ci = it->second;
            column_type tp = ci->get_column_type();
            col_types[i] = tp;
            
            switch (tp){
            case fixed:
                low_bounds[i] = ci->get_fixed_value();
                upper_bounds[i] = ci->get_fixed_value();
                break;
            case boxed:
                low_bounds[i] = ci->get_low_bound();
                upper_bounds[i] = ci->get_upper_bound();
                break;
            case low_bound:
                low_bounds[i] = ci->get_low_bound();
                break;
            case upper_bound:
                upper_bounds[i] = ci->get_upper_bound();
                
            default: 
                lean_assert(false);
                break; // do nothing
            }
            i++;
        }
    }
    
    void flatten_row(unsigned row_index,
                     std::unordered_map<unsigned, T> & row,
                     std::vector<column_type> & col_types,
                     std::vector<X> & low_bounds,
                     std::vector<X> & upper_bounds,
                     std::unordered_map<unsigned, unsigned> & from_flat_arrays_to_orig,
                     std::vector<std::pair<T, unsigned>> & vector) {
        unsigned row_size = row.size();

        auto ct = m_constraints.find(row_index);
        lean_assert (ct != m_constraints.end());
        lp_constraint<T, X> &constr = ct->second;

        if (constr.m_relation != Equal) row_size ++;
        
        low_bounds.resize(row_size);
        upper_bounds.resize(row_size);
        col_types.resize(row_size);
        flatten_row_with_allocated_vectors(row, col_types, low_bounds, upper_bounds, from_flat_arrays_to_orig, vector);
        unsigned i = row_size - 1;
        if (constr.m_relation == Less_or_equal) {
            vector.emplace_back(one_of_type<T>(), i);
            col_types[i] = low_bound;
            low_bounds[i] = zero_of_type<X>();
        } else if (constr.m_relation == Greater_or_equal) {
            vector.emplace_back(-one_of_type<T>(), i);
            col_types[i] = low_bound;
            low_bounds[i] = zero_of_type<X>();
        }
        // in those cases above i is not mapped to any variable of the solver            
        print_linear_combination_of_column_indices(vector, std::cout);
        std::cout << std::endl;
    }

    
    void analyse_flattened_row(unsigned row_index,
                               std::vector<std::pair<T, unsigned>>& row_vector,
                               std::vector<column_type> & col_types,
                               std::vector<X> & low_bounds,
                               std::vector<X> & upper_bounds,
                               std::vector<implied_bound_evidence_signature<T, X>> & evidences) {
        linear_combination_iterator_on_vector<T, X> it(row_vector);
        auto ct = m_constraints.find(row_index);
        lean_assert (ct != m_constraints.end());
        auto &constr = ct->second;
        const T & rs = constr.m_rs;
        bound_analyzer_on_row<T, X>::analyze_row(it, low_bounds, upper_bounds, rs, col_types, evidences);
        if (evidences.size() > 0) 
            std::cout << "found " << evidences.size() << " evidences" << std::endl;
    }

    bool check_can_be_fixed(column_info<X> * ci) {
         if ((!ci->upper_bound_is_set()) || (!ci->low_bound_is_set()))
            return false;
        // ok, both bounds are set
         bool at_least_one_is_strict = ci->upper_bound_is_strict() || ci->low_bound_is_strict();
         
         if (at_least_one_is_strict)
             return false;

         return m_settings.abs_val_is_smaller_than_drop_tolerance(ci->get_upper_bound() - ci->get_low_bound()); 
    }

    void process_evidence_when_lb(implied_bound_evidence_signature<T,X> & evidence, column_info<X> *ci, row_tighten_stats & st) {
        std::cout << "lb\n ";
#if LEAN_DEBUG
        if (ci->low_bound_is_set()) {
            X delta = evidence.m_bound - ci->get_low_bound();            
            lean_assert(numeric_traits<X>::is_pos(delta));
            if(m_settings.abs_val_is_smaller_than_primal_feasibility_tolerance(delta))
                return;
        }
#endif
        ci->set_low_bound(evidence.m_bound);
        if (ci->is_infeasible()) {
            set_status(INFEASIBLE);
            return;
        }
        lean_assert(!ci->is_fixed());
        if (check_can_be_fixed(ci)) {
            ci->set_fixed_value(ci->get_low_bound());
            st.n_of_fixed++;
        } else {
            st.n_of_new_bounds++;
        }
    }


    void process_evidence_when_ub(implied_bound_evidence_signature<T,X> & evidence, column_info<X> *ci, row_tighten_stats & st) {
#if LEAN_DEBUG
        if (ci->upper_bound_is_set()) {
            X delta = ci->get_upper_bound() - evidence.m_bound;
            lean_assert(numeric_traits<X>::is_pos(delta));
            if (m_settings.abs_val_is_smaller_than_primal_feasibility_tolerance(delta))
                return;
        }
#endif
       
        ci->set_upper_bound(evidence.m_bound);
        if (ci->is_infeasible()) {
            set_status(INFEASIBLE);
            return;
        }
        lean_assert(!ci->is_fixed());
        if (check_can_be_fixed(ci)) {
            ci->set_fixed_value(ci->get_low_bound());
            st.n_of_fixed++;
        } else {
            st.n_of_new_bounds++;
        }

    }

    
    void process_evidence(implied_bound_evidence_signature<T, X> & evidence, unsigned j, row_tighten_stats & st) {
        auto it =  m_map_from_var_index_to_column_info.find(j);
        lean_assert(it != m_map_from_var_index_to_column_info.end());
        column_info<X> *ci;
        try_get_val(m_map_from_var_index_to_column_info, j, ci);
        std::cout << "got ci " << ci->get_name() << std::endl;
        if (evidence.m_low_bound) {
            process_evidence_when_lb(evidence, ci, st);
        } else {
            process_evidence_when_ub(evidence, ci, st);
        }
        
    }
    
    void process_evidences(std::vector<column_type> & col_types,
                           std::vector<X> & low_bounds,
                           std::vector<X> & upper_bounds,
                           std::vector<implied_bound_evidence_signature<T, X>> & evidences,
                           std::unordered_map<unsigned, unsigned> & from_flat_arrays_to_orig, row_tighten_stats & st) {
        for (auto & ev: evidences) {
            auto it = from_flat_arrays_to_orig.find(ev.m_j);
            if (it == from_flat_arrays_to_orig.end())
                continue;
            
            process_evidence(ev, it->second, st);
        }
        st.is_obsolete = st.n_of_fixed == from_flat_arrays_to_orig.size();
    }

    void analyse_row(unsigned row_index, std::unordered_map<unsigned, T> & row, row_tighten_stats & row_stats) {
        std::vector<column_type> col_types;
        std::vector<X> low_bounds;
        std::vector<X> upper_bounds;
        std::unordered_map<unsigned, unsigned> from_flat_arrays_to_orig;
        std::vector<std::pair<T, unsigned>> row_vector;
        
        flatten_row(row_index, row, col_types, low_bounds, upper_bounds, from_flat_arrays_to_orig, row_vector);
        std::vector<implied_bound_evidence_signature<T, X>> evidences;
        analyse_flattened_row(row_index, row_vector, col_types, low_bounds, upper_bounds, evidences);
        process_evidences(col_types, low_bounds, upper_bounds, evidences, from_flat_arrays_to_orig, row_stats);
    }
    
    unsigned cleanup_tighten_some_rows() {
        std::vector<unsigned> rows_to_delete;
        unsigned n_of_fixed_vars_total = 0;
        unsigned n_of_new_bounds_total = 0;
        unsigned n_of_deleted_rows_total = 0;
        unsigned n_of_fixed_vars;
        unsigned n_of_new_bounds;
        unsigned n_of_deleted_rows;
        do {
            n_of_fixed_vars = 0;
            n_of_new_bounds = 0;
            n_of_deleted_rows = 0;
            
            for (auto & t : m_A_values) {
                row_tighten_stats row_stats;
                analyse_row(t.first, t.second, row_stats);
                if (row_stats.is_obsolete) {
                    rows_to_delete.push_back(t.first);
                }
            
                if (m_status == lp_status::INFEASIBLE) {
                    return 0;
                }
                
                n_of_new_bounds += row_stats.n_of_new_bounds;
                n_of_fixed_vars += row_stats.n_of_fixed;
            }

            if (rows_to_delete.size() > 0) {
                n_of_deleted_rows += rows_to_delete.size();
                for (unsigned k : rows_to_delete) {
                    m_A_values.erase(k);
                }
            }
            remove_fixed_or_zero_columns();
            n_of_deleted_rows_total+= n_of_deleted_rows;
            n_of_new_bounds_total += n_of_new_bounds;
            n_of_fixed_vars_total += n_of_fixed_vars;
        } while (n_of_fixed_vars || n_of_new_bounds || n_of_deleted_rows);
        
        std::cout << "total deleted rows " << n_of_deleted_rows_total << ", fixed vars " <<
            n_of_fixed_vars_total << ", found bounds " << n_of_new_bounds_total << std::endl;
        return n_of_new_bounds_total + n_of_fixed_vars_total + n_of_deleted_rows_total;
    }
    
public:
    lp_settings & settings() { return m_settings;}
};
}
