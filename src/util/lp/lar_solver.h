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

struct column_info_with_cls { // column_info_with canonic_left_side
    canonic_left_side  m_canonic_left_side;
    column_info<mpq> m_column_info;
    bool operator!=(const column_info_with_cls & c) const {
        return !(*this == c);
    }

    bool operator==(const column_info_with_cls & c) const {
        return m_canonic_left_side==c.m_canonic_left_side && m_column_info == c.m_column_info;
    }
    // constructor
    column_info_with_cls(): m_column_info(static_cast<unsigned>(-1)) {}

    // constructor
    column_info_with_cls(const canonic_left_side & cls) : m_canonic_left_side(cls), m_column_info(static_cast<unsigned>(-1)) {}
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
};

class lar_solver : public column_namer {
    //////////////////// fields //////////////////////////
    stacked_value<lp_status> m_status = UNKNOWN;
    stacked_map<std::string, var_index> m_var_names_to_var_index;
    stacked_map<canonic_left_side, ul_pair, hash_and_equal_of_canonic_left_side_struct, hash_and_equal_of_canonic_left_side_struct> m_map_of_canonic_left_sides;
    stacked_vector<lar_normalized_constraint> m_normalized_constraints;
    stacked_map<var_index, column_info_with_cls> m_map_from_var_index_to_column_info_with_cls;
    lar_core_solver_parameter_struct<mpq, numeric_pair<mpq>> m_lar_core_solver_params;
    lar_core_solver<mpq, numeric_pair<mpq>> m_mpq_lar_core_solver;
    stacked_value<canonic_left_side> m_infeasible_canonic_left_side; // such can be found at the initialization step
    stacked_vector<lar_term> m_terms;
    const var_index m_terms_start_index = 1000000;
    
    ////////////////// methods ////////////////////////////////
    static_matrix<mpq, numeric_pair<mpq>> & A() { return m_lar_core_solver_params.m_A;}
    canonic_left_side create_or_fetch_existing_left_side(const std::vector<std::pair<mpq, var_index>>& left_side_par);
    static mpq find_ratio_of_original_constraint_to_normalized(const canonic_left_side & ls, const lar_constraint & constraint);

    void add_canonic_left_side_for_var(var_index i, std::string var_name);

    void map_left_side_to_A_of_core_solver(const canonic_left_side &  left_side, var_index vj);

    bool valid_index(unsigned j) { return static_cast<int>(j) >= 0;}


    // this adds a row to A
    template <typename U, typename V>
    void fill_row_of_A(static_matrix<U, V> & A, const canonic_left_side & ls);

    unsigned number_or_nontrivial_left_sides() const
    {
        unsigned ret = 0;
        for (auto & p : m_map_of_canonic_left_sides()) {
            if (p.first.size() > 1)
                ret++;
        }
        return ret;
    }
    template <typename U, typename V>
    void create_matrix_A(static_matrix<U, V> & A);
    template <typename U, typename V>
    void copy_from_mpq_matrix(static_matrix<U,V> & matr);
    
    // void fill_column_info_names() {
    //     for (unsigned j = 0; j < m_A.column_count(); j++) {
    //         column_info<mpq> t;
    //         m_column_infos.push_back(t);
    //         if (j < m_map_from_var_index_to_name_left_side_pair.size()) {
    //             m_column_infos.back().set_name(m_map_from_var_index_to_name_left_side_pair[j]);
    //         } else {
    //             string pref("_s_");
    //             m_column_infos.back().set_name(pref + T_to_string(j));
    //         }
    //         m_column_names
    //     }
    // }
    void set_upper_bound_for_column_info(constraint_index i, const lar_normalized_constraint & norm_constr);

    bool try_to_set_fixed(column_info<mpq> & ci);

    void set_low_bound_for_column_info(constraint_index i, const lar_normalized_constraint & norm_constr);

    void update_column_info_of_normalized_constraint(constraint_index i, const lar_normalized_constraint & norm_constr);

    column_type get_column_type(const column_info<mpq> & ci);

    std::string get_column_name(unsigned j) const override;

    void fill_column_types();

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
    lp_settings & settings() { return m_lar_core_solver_params.m_settings;}

    lp_settings const & settings() const { return m_lar_core_solver_params.m_settings;}

    void clear() {lean_assert(false); // not implemented
    }

    lar_solver() : m_mpq_lar_core_solver(m_lar_core_solver_params.m_x,
                                     m_lar_core_solver_params.m_column_types,
                                     m_lar_core_solver_params.m_low_bounds,
                                     m_lar_core_solver_params.m_upper_bounds,
                                     m_lar_core_solver_params.m_basis,
                                     m_lar_core_solver_params.m_A,
                                     m_lar_core_solver_params.m_settings,
                                         *this) {
    }

    virtual ~lar_solver(){}

    bool all_constrained_variables_are_registered(const std::vector<std::pair<mpq, var_index>>& left_side);

    var_index add_var(std::string s);

    constraint_index add_var_bound(var_index j, lconstraint_kind kind_par, mpq right_side_par)  {
        std::vector<std::pair<mpq, var_index>> left_side;
        left_side.emplace_back(1, j);
        return add_constraint(left_side, kind_par, right_side_par);
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

    bool the_evidence_is_correct();

    void update_column_info_of_normalized_constraints();

    mpq sum_of_right_sides_of_evidence(const std::vector<std::pair<mpq, unsigned>> & evidence);
    void prepare_independently_of_numeric_type();

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

    void print_constraints(std::ostream & out);

    void print_constraint(constraint_index ci, std::ostream & out);

    void print_canonic_left_side(const canonic_left_side & c, std::ostream & out);

    void print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out);

    mpq get_infeasibility_of_solution(std::unordered_map<std::string, mpq> & solution);

    mpq get_infeasibility_of_constraint(const lar_normalized_constraint & norm_constr, std::unordered_map<std::string, mpq> & solution);

    mpq get_canonic_left_side_val(const canonic_left_side & ls, std::unordered_map<std::string, mpq> & solution);

    mpq get_left_side_val(const lar_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const;

    void print_constraint(const lar_base_constraint * c, std::ostream & out);
    unsigned get_total_iterations() const { return m_mpq_lar_core_solver.total_iterations(); }
// see http://research.microsoft.com/projects/z3/smt07.pdf
// This method searches for a feasible solution with as many different values of variables, reverenced in vars, as it can find
// Attention, after a call to this method the non-basic variables don't necesserarly stick to their bounds anymore
    void random_update(unsigned sz, var_index const* vars);
    void try_pivot_fixed_vars_from_basis();
    void fill_var_set_for_random_update(unsigned sz, var_index const * vars, std::vector<unsigned>& column_list);
    std::vector<unsigned> get_list_of_all_var_indices() const {
        std::vector<unsigned> ret;
        for (auto t : m_map_from_var_index_to_column_info_with_cls())
            ret.push_back(t.first);
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
    void add_row_to_A(const canonic_left_side & ls);
    void fill_basis_from_canonic_left_sides() {
        auto & b = m_lar_core_solver_params.m_basis;
        b.clear();
        for (auto & t : m_map_of_canonic_left_sides()) {
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
        return m_lar_core_solver_params.m_settings.use_double_solver_for_lar
            && m_lar_core_solver_params.m_A.row_count() > 0; // todo, add more conditions
    }
};
}
