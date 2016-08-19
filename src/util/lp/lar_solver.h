/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <utility>
#include "util/debug.h"
#include "util/buffer.h"
#include <unordered_map>
#include <unordered_set>
#include <string>
#include "util/lp/lar_constraints.h"
#include <functional>
#include "util/lp/lar_core_solver.h"
#include <algorithm>
#include "util/lp/numeric_pair.h"
#include "util/lp/lar_solution_signature.h"
#include "util/lp/scaler.h"
#include "util/lp/lp_primal_core_solver.h"
#include "util/lp/lar_core_solver_parameter_struct.h"
#include "util/lp/random_updater.h"
#include <stack>
#include "util/lp/stacked_map.h"
#include "util/lp/stacked_value.h"
#include "util/lp/stacked_vector.h"
#include "util/lp/stacked_unordered_set.h"
namespace lean {
template <typename V>
struct conversion_helper {
    static V get_low_bound(const column_info<mpq> & ci) {
        return V(ci.get_low_bound(), ci.low_bound_is_strict()? 1 : 0);
    }

    static V get_upper_bound(const column_info<mpq> & ci) {
        return V(ci.get_upper_bound(), ci.upper_bound_is_strict()? -1 : 0);
    }
};

template<>
struct conversion_helper <double> {
    static double get_low_bound(const column_info<mpq> & ci);
    static double get_upper_bound(const column_info<mpq> & ci);
};

struct lar_term {
    // the term evaluates to sum of m_coeffs + m_v
    std::vector<std::pair<mpq, var_index>> m_coeffs;
    mpq m_v;
    lar_term() {}
    lar_term(const std::vector<std::pair<mpq, var_index>> coeffs,
             const mpq & v) : m_coeffs(coeffs), m_v(v) {
    }
    bool operator==(const lar_term & a) const {  return m_coeffs == a.m_coeffs && m_v == a.m_v;}
    bool operator!=(const lar_term & a) const {  return ! (*this == a);}
};

class lar_solver : public column_namer {
    //////////////////// fields //////////////////////////
    // fields used in m_mpq_lar_core_solver
    std::vector<numeric_pair<mpq>> m_x; // the solution
    stacked_vector<column_type> m_column_types;
    stacked_vector<numeric_pair<mpq>> m_low_bounds;
    stacked_vector<numeric_pair<mpq>> m_upper_bounds;
    stacked_vector<unsigned> m_sorted_basis;
    std::vector<unsigned> m_basis;
    std::vector<unsigned> m_nbasis;
    std::vector<int> m_heading;
    static_matrix<mpq, numeric_pair<mpq>> m_A;
    lp_settings m_settings;
    // end of fields used in m_mpq_lar_core_solver
    
    stacked_value<lp_status> m_status = UNKNOWN;
    stacked_map<std::string, var_index> m_var_names_to_var_index;
    std::vector<std::string> m_column_names;
    stacked_map<canonic_left_side, ul_pair, hash_and_equal_of_canonic_left_side_struct, hash_and_equal_of_canonic_left_side_struct> m_map_of_canonic_left_sides_to_ul_pairs;
    stacked_vector<lar_normalized_constraint> m_normalized_constraints;
    stacked_vector<canonic_left_side> m_vec_of_canonic_left_sides;
    // the set of column indices j such that m_x[j] does not satisfy one of its bounds
    std::unordered_set<var_index> m_columns_out_of_bounds;
    
    lar_core_solver<mpq, numeric_pair<mpq>> m_mpq_lar_core_solver;
    stacked_value<canonic_left_side> m_infeasible_canonic_left_side; // such can be found at the initialization step
    stacked_vector<lar_term> m_terms;
    const var_index m_terms_start_index = 1000000;
    
    ////////////////// methods ////////////////////////////////
    static_matrix<mpq, numeric_pair<mpq>> & A() { return m_A;}
    canonic_left_side create_or_fetch_existing_left_side(const std::vector<std::pair<mpq, var_index>>& left_side_par, var_index & j);
    static mpq find_ratio_of_original_constraint_to_normalized(const canonic_left_side & ls, const lar_constraint & constraint);

    void add_canonic_left_side_for_var(var_index i, std::string var_name);

    bool valid_index(unsigned j) { return static_cast<int>(j) >= 0;}

    void fill_last_row_of_A(static_matrix<mpq, numeric_pair<mpq>> & A, const canonic_left_side & ls);

    unsigned number_or_nontrivial_left_sides() const
    {
        unsigned ret = 0;
        for (auto & p : m_map_of_canonic_left_sides_to_ul_pairs()) {
            if (p.first.size() > 1)
                ret++;
        }
        return ret;
    }
    template <typename U, typename V>
    void create_matrix_A(static_matrix<U, V> & A);
    template <typename U, typename V>
    void copy_from_mpq_matrix(static_matrix<U,V> & matr);
    
    void set_upper_bound_for_column_info(constraint_index i, const lar_normalized_constraint & norm_constr);

    bool try_to_set_fixed(column_info<mpq> & ci);

    void set_low_bound_for_column_info(constraint_index i, const lar_normalized_constraint & norm_constr);

    column_type get_column_type(const column_info<mpq> & ci);

    std::string get_column_name(unsigned j) const override;

    template <typename V>
    void fill_bounds_for_core_solver(std::vector<V> & lb, std::vector<V> & ub);


    template <typename V>
    void resize_and_init_x_with_zeros(std::vector<V> & x);

    template <typename V>
    void resize_and_init_x_with_signature(std::vector<V> & x, std::vector<V> & low_bound,
                                          std::vector<V> & upper_bound, const lar_solution_signature & signature);

    template <typename V> V get_column_val(std::vector<V> & low_bound, std::vector<V> & upper_bound, non_basic_column_value_position pos_type, unsigned j);

    void register_in_map(std::unordered_map<var_index, mpq> & coeffs, const lar_constraint & cn, const mpq & a);

    const column_info<mpq> & get_column_info_from_var_index(var_index vi) const;

public:
    lp_settings & settings() { return m_settings;}

    lp_settings const & settings() const { return m_settings;}

    void clear() {lean_assert(false); // not implemented
    }


    // the cast here is safe because the solver with rationals does not change the bounds, only the solver with doubles does
    
    lar_solver() : m_mpq_lar_core_solver(m_x,
                                         m_column_types(),
                                         const_cast<std::vector<numeric_pair<mpq>> &>(m_low_bounds()),
                                         const_cast<std::vector<numeric_pair<mpq>> &>(m_upper_bounds()),
                                         m_basis,
                                         m_nbasis,
                                         m_heading,
                                         m_A,
                                         m_settings,
                                         *this,
                                         m_columns_out_of_bounds) {}

    virtual ~lar_solver(){}

    bool all_constrained_variables_are_registered(const std::vector<std::pair<mpq, var_index>>& left_side);

    var_index add_var(std::string s);

    bool is_term(unsigned j) const {
        return j >= m_terms_start_index && j - m_terms_start_index < m_terms.size();
    }

    unsigned adjust_term_index(unsigned j) const {
        lean_assert(is_term(j));
        return j - m_terms_start_index;
    }
    
    constraint_index add_var_bound(var_index j, lconstraint_kind kind, mpq right_side)  {
        if (j < m_A.column_count()) { // j is a var
            std::vector<std::pair<mpq, var_index>> left_side;
            left_side.emplace_back(1, j);
            return add_constraint(left_side, kind, right_side);
        }
        // it is a term
        return add_constraint(m_terms()[adjust_term_index(j)].m_coeffs, kind, right_side);
    }

    constraint_index add_constraint(const std::vector<std::pair<mpq, var_index>>& left_side, lconstraint_kind kind_par, mpq right_side_par);

    bool get_constraint(constraint_index ci, lar_constraint& ci_constr) const  {
        if (ci < m_normalized_constraints().size()) {
            ci_constr =  m_normalized_constraints()[ci].m_origin_constraint;
            return true;
        }
        return false;
    }

    bool all_constraints_hold() const;

    bool constraint_holds(const lar_constraint & constr, std::unordered_map<var_index, mpq> & var_map) const;

    lp_status get_status() const { return m_status;}

    void solve_with_core_solver();

    bool the_relations_are_of_same_type(const std::vector<std::pair<mpq, unsigned>> & evidence, lconstraint_kind & the_kind_of_sum);

    bool the_left_sides_sum_to_zero(const std::vector<std::pair<mpq, unsigned>> & evidence);

    bool the_right_sides_do_not_sum_to_zero(const std::vector<std::pair<mpq, unsigned>> & evidence);

    bool evidence_is_correct();

    mpq sum_of_right_sides_of_evidence(const std::vector<std::pair<mpq, unsigned>> & evidence);

    template <typename U, typename V>
    void prepare_core_solver_fields(static_matrix<U, V> & A, std::vector<V> & x,
                                     std::vector<V> & low_bound,
                                     std::vector<V> & upper_bound);

    template <typename U, typename V>
    void prepare_core_solver_fields_with_signature(static_matrix<U, V> & A, std::vector<V> & x,
                                                   std::vector<V> & low_bound,
                                                   std::vector<V> & upper_bound, const lar_solution_signature & signature);

    void find_solution_signature_with_doubles(lar_solution_signature & signature);

    template <typename U, typename V>
    void extract_signature_from_lp_core_solver(lp_primal_core_solver<U, V> & core_solver, lar_solution_signature & signature);

    void solve_on_signature(const lar_solution_signature & signature);

    lp_status solve();

    void get_infeasibility_evidence(std::vector<std::pair<mpq, constraint_index>> & evidence);
    void fill_evidence_from_canonic_left_side(std::vector<std::pair<mpq, constraint_index>> & evidence);

    void get_infeasibility_evidence_for_inf_sign(std::vector<std::pair<mpq, constraint_index>> & evidence,
                                                 const std::vector<std::pair<mpq, unsigned>> & inf_row,
                                                 int inf_sign);


    mpq find_delta_for_strict_bounds() const;

    void restrict_delta_on_low_bound_column(mpq& delta, unsigned j) const;
    void restrict_delta_on_upper_bound(mpq& delta, unsigned j) const;

    void get_model(std::unordered_map<var_index, mpq> & variable_values) const;

    std::string get_variable_name(var_index vi) const;

    void print_constraints(std::ostream & out) const ;

    void print_constraint(constraint_index ci, std::ostream & out) const ;

    void print_canonic_left_side(const canonic_left_side & c, std::ostream & out) const ;

    void print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out) const ;

    void print_term(lar_term const& term, std::ostream & out) const ;

    mpq get_infeasibility_of_solution(std::unordered_map<std::string, mpq> & solution);

    mpq get_infeasibility_of_constraint(const lar_normalized_constraint & norm_constr, std::unordered_map<std::string, mpq> & solution);

    mpq get_canonic_left_side_val(const canonic_left_side & ls, std::unordered_map<std::string, mpq> & solution);

    mpq get_left_side_val(const lar_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const;

    void print_constraint(const lar_base_constraint * c, std::ostream & out) const;
    unsigned get_total_iterations() const { return m_mpq_lar_core_solver.total_iterations(); }
// see http://research.microsoft.com/projects/z3/smt07.pdf
// This method searches for a feasible solution with as many different values of variables, reverenced in vars, as it can find
// Attention, after a call to this method the non-basic variables don't necesserarly stick to their bounds anymore
    void random_update(unsigned sz, var_index const* vars);
    void try_pivot_fixed_vars_from_basis();
    void fill_var_set_for_random_update(unsigned sz, var_index const * vars, std::vector<unsigned>& column_list);
    std::vector<unsigned> get_list_of_all_var_indices() const {
        std::vector<unsigned> ret;
        for (unsigned j = 0; j < m_heading.size(); j++)
            ret.push_back(j);
        return ret;
    }
    void push();
    void pop();
    void pop(unsigned k);
    std::vector<constraint_index> get_all_constraint_indices() const {
        std::vector<constraint_index> ret;
        constraint_index i = 0;
        while ( i < m_normalized_constraints().size())
            ret.push_back(i++);
        return ret;
    }
    std::vector<std::string> get_all_var_names() const {
        std::vector<std::string> ret;
        for (auto & it : m_var_names_to_var_index())
            ret.push_back(it.first);
        return ret;
    }

    void fill_basis_from_canonic_left_sides() {
        auto & b = m_basis;
        b.clear();
        for (auto & t : m_map_of_canonic_left_sides_to_ul_pairs()) {
            if (t.first.size() > 1)
                b.push_back(t.second.m_additional_var_index);
        }
    }
    var_index add_term(const std::vector<std::pair<mpq, var_index>> & m_coeffs,
                      const mpq &m_v) {
        m_terms.push_back(lar_term(m_coeffs, m_v));
        return m_terms_start_index + m_terms.size() - 1;
    }

    const lar_term &  get_term(unsigned j) const {
        lean_assert(j >= m_terms_start_index);
        return m_terms[j - m_terms_start_index];
    }

 
    bool need_to_presolve_with_double_solver() const {
        return m_settings.use_double_solver_for_lar
            && m_A.row_count() > 0; // todo, add more conditions
    }

    bool low_bound_is_set(unsigned j) const {
        switch (m_column_types[j]) {
        case free_column:
        case upper_bound:
            return false;
        case low_bound:
        case boxed:
        case fixed:
            return true;
        default:
            lean_assert(false);
        }
        return false;
    }
    bool upper_bound_is_set(unsigned j) const {
        switch (m_column_types[j]) {
        case free_column:
        case low_bound:
            return false;
        case upper_bound:
        case boxed:
        case fixed:
            return true;
        default:
            lean_assert(false);
        }
        return false;
    }

    void pop_core_solver_params() {
        pop_core_solver_params(1);
    }
     void pop_core_solver_params(unsigned k) {
        m_A.pop(k);
     }

    void add_new_var_to_core_fields(bool register_in_basis, numeric_pair<mpq> val) {
        unsigned i = m_A.column_count();
        m_A.add_column();
        lean_assert(m_x.size() == i);
        lean_assert(m_column_types.size() == i);
        m_column_types.push_back(free_column);
        lean_assert(m_low_bounds.size() == i && m_upper_bounds.size() == i);
        // we need to insert some value, does not matter which
        m_low_bounds.push_back(zero_of_type<numeric_pair<mpq>>());
        m_upper_bounds.push_back(zero_of_type<numeric_pair<mpq>>());
        m_x.push_back(val);

        lean_assert(m_heading.size() == i); // as m_A.column_count() on the entry to the method
        lean_assert(m_nbasis.size() == i - m_A.row_count());
        if (register_in_basis) {
            m_A.add_row();
            m_heading.push_back(m_basis.size());
            m_basis.push_back(i);
        }else {
            m_heading.push_back(- static_cast<int>(m_nbasis.size()) - 1);
            m_nbasis.push_back(i);
        }
    }

    void register_new_var_name(std::string s) {
        lean_assert(!m_var_names_to_var_index.contains(s));
        unsigned j = m_var_names_to_var_index.size();
        m_var_names_to_var_index[s] = j;
        lean_assert(m_column_names.size() == j);
        m_column_names.push_back(s);
    }


    void set_upper_bound_witness(constraint_index ci) {
        const lar_normalized_constraint & a = m_normalized_constraints[ci];
        auto & cls = a.m_canonic_left_side;
        ul_pair ul = m_map_of_canonic_left_sides_to_ul_pairs[cls];
        ul.m_upper_bound_witness = ci;
        m_map_of_canonic_left_sides_to_ul_pairs[cls] = ul;
    }

    void set_low_bound_witness(constraint_index ci) {
        const lar_normalized_constraint & a = m_normalized_constraints[ci];
        auto & cls = a.m_canonic_left_side;
        ul_pair ul = m_map_of_canonic_left_sides_to_ul_pairs[cls];
        ul.m_low_bound_witness = ci;
        m_map_of_canonic_left_sides_to_ul_pairs[cls] = ul;
    }

    
    void update_free_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_ind) {
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            m_column_types[j] = upper_bound;
            lean_assert(m_column_types[j] == upper_bound);
            lean_assert(m_upper_bounds.size() > j);
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                m_upper_bounds[j] = up;
                if (m_heading[j] < 0)
                    m_x[j] = up;
            }
            set_upper_bound_witness(constr_ind);
            break;
        case GT:
            y_of_bound = 1;
        case GE:
            m_column_types[j] = low_bound;
            lean_assert(m_upper_bounds.size() > j);
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                m_low_bounds[j] = low;
                if (m_heading[j] < 0)
                    m_x[j] = low;
            }
            set_low_bound_witness(constr_ind);
            break;
        case EQ:
            m_column_types[j] = fixed;
            m_low_bounds[j] = m_upper_bounds[j] =
                m_x[j] = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            set_upper_bound_witness(constr_ind);
            set_low_bound_witness(constr_ind);
            break;

        default:
            lean_unreachable();
                
        }
    }

    void update_upper_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_column_types[j] == upper_bound);
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                if (up < m_upper_bounds()[j]) {
                    m_upper_bounds[j] = up;
                    set_upper_bound_witness(ci);
                    if (m_heading[j] < 0)
                        m_x[j] = up;
                }
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            m_column_types[j] = boxed;
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                m_low_bounds[j] = low;
                set_low_bound_witness(ci);
                if (m_heading[j] < 0)
                    m_x[j] = low;
                if (low > m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_column_types[j] = m_low_bounds()[j] < m_upper_bounds()[j]? boxed : fixed;
                }                     
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v > m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    set_low_bound_witness(ci);
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_low_bounds[j] = m_upper_bounds[j] = v;
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_column_types[j] = fixed;
                }
                break;
            }
            break;

        default:
            lean_unreachable();
                
        }
    }
    
    void update_boxed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_status == INFEASIBLE || m_column_types[j] == boxed && m_low_bounds()[j] < m_upper_bounds()[j]);
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                if (up < m_upper_bounds[j]) {
                    m_upper_bounds[j] = up;
                    set_upper_bound_witness(ci);
                }
                if (m_heading[j] < 0)
                    m_x[j] = up;

                if (up < m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    if (m_low_bounds()[j] == m_upper_bounds()[j])
                        m_column_types[j] = fixed;
                }                    
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low > m_low_bounds[j]) {
                    m_low_bounds[j] = low;
                    if (m_heading[j] < 0)
                        m_x[j] = low;
                    set_low_bound_witness(ci);
                }
                if (low > m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else if ( low == m_upper_bounds[j]) {
                    m_column_types[j] = fixed;
                }
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v < m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else if (v > m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);                    
                } else {
                    m_low_bounds[j] = m_upper_bounds[j] = v;
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_column_types[j] = fixed;
                }
                if (m_heading[j] < 0)
                    m_x[j] = v;
                
                break;
            }

        default:
            lean_unreachable();
                
        }
    }
    void update_low_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_column_types[j] == low_bound);
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                m_upper_bounds[j] = up;
                set_upper_bound_witness(ci);
                if (m_heading[j] < 0)
                    m_x[j] = up;

                if (up < m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_column_types[j] = m_low_bounds()[j] < m_upper_bounds()[j]? boxed : fixed;
                }                    
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low > m_low_bounds[j]) {
                    m_low_bounds[j] = low;
                    if (m_heading[j] < 0)
                        m_x[j] = low;
                    set_low_bound_witness(ci);
                }
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v < m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else {
                    m_low_bounds[j] = m_upper_bounds[j] = v;
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_column_types[j] = fixed;
                }
                if (m_heading[j] < 0)
                    m_x[j] = v;
                break;
            }

        default:
            lean_unreachable();
                
        }
    }

    void update_fixed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_status == INFEASIBLE || m_column_types[j] == fixed && m_low_bounds()[j] == m_upper_bounds()[j]);
        lean_assert(m_status == INFEASIBLE || m_low_bounds()[j].y.is_zero() && m_upper_bounds()[j].y.is_zero());
        auto v = numeric_pair<mpq>(right_side, mpq(0));
        
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
                if (v <= m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);
                }                   
                break;
        case LE:
            {
                if (v < m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);
                }                   
            }
            break;
        case GT:
            {
                if (v >= m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);
                }
            }
            break;
        case GE:            
            {
                if (v > m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);
                }
            }
            break;
        case EQ:
            {
                if (v < m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else if (v > m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);                    
                } 
                break;
            }

        default:
            lean_unreachable();
                
        }
    }
    
    void update_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index) {
        switch(m_column_types[j]) {
        case free_column:
            update_free_column_type_and_bound(j, kind, right_side, constr_index);
            break;
        case boxed:
            update_boxed_column_type_and_bound(j, kind, right_side, constr_index);
            break;
        case low_bound:
            update_low_bound_column_type_and_bound(j, kind, right_side, constr_index);
            break;
        case upper_bound:
            update_upper_bound_column_type_and_bound(j, kind, right_side, constr_index);
            break;
        case fixed:
            update_fixed_column_type_and_bound(j, kind, right_side, constr_index);
            break;
        default:
            lean_assert(false); // cannot be here
        }
        if (m_heading[j] >= 0) {
            if (m_mpq_lar_core_solver.column_is_feasible(j))
                m_columns_out_of_bounds.erase(j);
            else
                m_columns_out_of_bounds.insert(j);
        }
    }


    void substitute_terms(const mpq & mult, const std::vector<std::pair<mpq, var_index>>& left_side_with_terms,std::vector<std::pair<mpq, var_index>> &left_side, mpq & right_side) const {
        for (auto & t : left_side_with_terms) {
            if (t.second < m_terms_start_index) {
                lean_assert(t.second < m_A.column_count());
                left_side.push_back(std::pair<mpq, var_index>(mult * t.first, t.second));
            } else {
                const lar_term & term = m_terms[adjust_term_index(t.second)];
                substitute_terms(mult * t.first, term.m_coeffs, left_side, right_side);
                right_side -= mult * term.m_v;
            }
        }
    }

    void pop_basis(unsigned k) {
        // restore by using m_sorted
        m_sorted_basis.pop(k);
        m_heading.clear();
        m_heading.resize(m_A.column_count(), -1);
        m_basis.clear();
        for (unsigned i = 0; i < m_sorted_basis.size(); i++ ) {
            unsigned j = m_sorted_basis[i];
            m_heading[j] = i;
            m_basis.push_back(j);
        }
        
        m_nbasis.clear();
        for (unsigned j = 0; j < m_heading.size(); j++) {
            int & pos = m_heading[j]; // we are going to change it!
            if (pos < 0 ) { // j is in nbasis
                pos = -1 - static_cast<int>(m_nbasis.size());
                m_nbasis.push_back(j);
            }
        }
    }

    
    void sort_and_push_basis() {
        std::vector<unsigned> basis_copy(m_basis);
        std::sort(basis_copy.begin(), basis_copy.end());
        lean_assert(m_sorted_basis.size() <= m_basis.size());
        for (unsigned i = 0; i < m_basis.size();i++) {
            if (i == m_sorted_basis.size()) {
                m_sorted_basis.push_back(m_basis[i]);
            } else {
                m_sorted_basis[i] = m_basis[i];
            }
        }
        m_sorted_basis.push();
    }
};
}
