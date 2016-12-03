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
#include "util/lp/scaler.h"
#include "util/lp/lp_primal_core_solver.h"
#include "util/lp/random_updater.h"
#include <stack>
#include "util/lp/stacked_map.h"
#include "util/lp/stacked_value.h"
#include "util/lp/stacked_vector.h"
#include "util/lp/stacked_unordered_set.h"
#include "util/lp/iterator_on_pivot_row.h"
#include "util/lp/implied_bound_evidence_signature.h"
#include "util/lp/bound_analyzer_on_row.h"
#include "util/lp/bound_evidence.h"
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

struct column_name_and_term_info {
    std::string m_name;
    // -1 means that the column does not represent a term
    int m_term_column_index = -1;
    int m_term_index_in_normalized_constraints = -1;
    column_name_and_term_info() {}
    column_name_and_term_info(std::string name) : m_name(name) {}
    column_name_and_term_info(std::string name,
                           int term_column_index,
                           int term_index_in_normalized_constraints) :
        m_name(name),
        m_term_column_index(term_column_index),
        m_term_index_in_normalized_constraints(term_index_in_normalized_constraints){}
    
    bool is_term() const { return m_term_column_index >= 0;}
};

class lar_solver : public column_namer {
    //////////////////// fields //////////////////////////
    // fields used in m_mpq_lar_core_solver
    lp_settings m_settings;
    // end of fields used in m_mpq_lar_core_solver
    
    stacked_value<lp_status> m_status = UNKNOWN;
    stacked_map<std::string, var_index> m_var_names_to_var_index;
    std::vector<column_name_and_term_info> m_columns_name_term;
    // for each column j its canonic_left_side can be found as m_vec_of_canonic_left_sides[j] 
    stacked_map<canonic_left_side, ul_pair, hash_and_equal_of_canonic_left_side_struct, hash_and_equal_of_canonic_left_side_struct> m_map_of_canonic_left_sides_to_ul_pairs;
    stacked_vector<lar_normalized_constraint> m_normalized_constraints;
    stacked_vector<canonic_left_side> m_vec_of_canonic_left_sides;
    int_set m_touched_columns;
    int_set m_touched_rows;
    lar_core_solver<mpq, numeric_pair<mpq>> m_mpq_lar_core_solver;
    stacked_value<canonic_left_side> m_infeasible_canonic_left_side; // such can be found at the initialization step
    indexed_vector<mpq> m_column_buffer;    
    
    ////////////////// methods ////////////////////////////////
    static_matrix<mpq, numeric_pair<mpq>> & A_r() { return m_mpq_lar_core_solver.m_r_A;}
    static_matrix<mpq, numeric_pair<mpq>> const & A_r() const { return m_mpq_lar_core_solver.m_r_A;}
    static_matrix<double, double> & A_d() { return m_mpq_lar_core_solver.m_d_A;}
    static_matrix<double, double > const & A_d() const { return m_mpq_lar_core_solver.m_d_A;}
    
    canonic_left_side create_or_fetch_existing_left_side(const std::vector<std::pair<mpq, var_index>>& left_side_par, var_index & j);
    static mpq find_ratio_of_original_constraint_to_normalized(const canonic_left_side & ls, const lar_constraint & constraint);

    void add_canonic_left_side_for_var(var_index i, std::string var_name);

    bool valid_index(unsigned j) { return static_cast<int>(j) >= 0;}

    void fill_last_row_of_A_r(static_matrix<mpq, numeric_pair<mpq>> & A, const canonic_left_side & ls);

    void fill_last_row_of_A_d(static_matrix<double, double> & A, const canonic_left_side & ls);

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
    
    bool try_to_set_fixed(column_info<mpq> & ci);

    column_type get_column_type(const column_info<mpq> & ci);

    std::string get_column_name(unsigned j) const override;

    template <typename V>
    void fill_bounds_for_core_solver(std::vector<V> & lb, std::vector<V> & ub);

    void register_in_map(std::unordered_map<var_index, mpq> & coeffs, const lar_constraint & cn, const mpq & a);

    const column_info<mpq> & get_column_info_from_var_index(var_index vi) const;

public:
    lp_settings & settings() { return m_settings;}

    lp_settings const & settings() const { return m_settings;}

    void clear() {lean_assert(false); // not implemented
    }


    lar_solver() : m_mpq_lar_core_solver(
                                         m_settings,
                                         *this
                                         )   {}

    virtual ~lar_solver(){}

    bool all_constrained_variables_are_registered(const std::vector<std::pair<mpq, var_index>>& left_side);

    var_index add_var(std::string s);

    numeric_pair<mpq> const& get_value(var_index vi) const { return m_mpq_lar_core_solver.m_r_x[vi]; }

    bool is_term(unsigned j) const {
        return m_columns_name_term[j].is_term();
    }

    unsigned adjust_term_index(unsigned j) const {
        return j;
    }
    
    constraint_index add_var_bound(var_index j, lconstraint_kind kind, const mpq & right_side)  {
        lean_assert(A_r().column_count() == A_d().column_count());
        lean_assert(j < A_r().column_count());
        const canonic_left_side& cls = m_vec_of_canonic_left_sides[j];
        return add_constraint_for_existing_left_side(cls, kind, right_side);
    }

 
    void print_bound_evidence(const bound_evidence& be, std::ostream & out) {
        out << "evidence\n";
        for (auto & p : be.m_evidence) {
            out << p.first << std::endl;
            print_constraint(p.second, out);
        }
        out << "after summing up the constraints we get\n";
        print_linear_combination_of_column_indices(m_vec_of_canonic_left_sides()[be.m_j].m_coeffs, out);
        out << " " << lconstraint_kind_string(be.m_kind) << " "  << be.m_bound << std::endl;
    }
    
    void bound_evidence_is_correct(bound_evidence & be) {
        std::unordered_map<unsigned, mpq> coeff_map;
        auto rs = zero_of_type<mpq>();
        unsigned n_of_G = 0, n_of_L = 0;
        bool strict = false;
        for (auto & it : be.m_evidence) {
            mpq coeff = it.first;
            constraint_index con_ind = it.second;
            const lar_normalized_constraint & norm_constr = m_normalized_constraints()[con_ind];
            const lar_constraint & constr = norm_constr.m_origin_constraint;
            lconstraint_kind kind = coeff.is_pos() ? constr.m_kind : flip_kind(constr.m_kind);
            register_in_map(coeff_map, constr, coeff);
            if (kind == GT || kind == LT)
                strict = true;
            if (kind == GE || kind == GT) n_of_G++;
            else if (kind == LE || kind == LT) n_of_L++;
            rs += coeff*constr.m_right_side;
        }
        lean_assert(n_of_G == 0 || n_of_L == 0);
        lconstraint_kind kind = n_of_G ? GE : (n_of_L ? LE : EQ);
        if (strict)
            kind = static_cast<lconstraint_kind>((static_cast<int>(kind) / 2));
      
        std::vector<std::pair<mpq, var_index>> coeffs;
        for (auto & p : coeff_map) {
            coeffs.emplace_back(p.second, p.first);
        }
        canonic_left_side cls(coeffs);
        lean_assert(cls.size() > 0);
        lean_assert(cls == m_vec_of_canonic_left_sides[be.m_j]);
        
        mpq c = coeff_map[coeffs[0].second];
        if (c.is_neg())
            kind = flip_kind(kind);
        lean_assert(kind == be.m_kind);
        lean_assert(be.m_bound == rs / c);
    }

    void analyze_new_bounds_on_row(std::vector<implied_bound_evidence_signature<mpq, numeric_pair<mpq>>>& evidence_vector, unsigned row_index) {
        iterator_on_pivot_row<mpq> it(m_mpq_lar_core_solver.get_pivot_row(), m_mpq_lar_core_solver.m_r_basis[row_index]); 
        bound_analyzer_on_row<mpq, numeric_pair<mpq>> ra_pos(it,
                                                             m_mpq_lar_core_solver.m_r_low_bounds(),
                                                             m_mpq_lar_core_solver.m_r_upper_bounds(),
                                                             zero_of_type<numeric_pair<mpq>>(),
                                                             m_mpq_lar_core_solver.m_column_types(),
                                                             evidence_vector,
                                                             true);
        ra_pos.analyze();
    }

    void calculate_implied_bound_evidences(unsigned i,
                                           std::vector<implied_bound_evidence_signature<mpq, numeric_pair<mpq>>>& evidence_vector) {
        m_mpq_lar_core_solver.calculate_pivot_row(i);
        analyze_new_bounds_on_row(evidence_vector, i);
    }
    void process_new_implied_evidence_for_low_bound(
                                                    implied_bound_evidence_signature<mpq, numeric_pair<mpq>>& implied_evidence, // not pushed yet
        std::vector<bound_evidence> & bound_evidences,
        std::unordered_map<unsigned, unsigned> & improved_low_bounds) {

        unsigned existing_index;
        if (try_get_val(improved_low_bounds, implied_evidence.m_j, existing_index)) {
            bound_evidence & be = bound_evidences[existing_index];
            be.m_evidence.clear();
            // we are improving the existent bound improve the existing bound
            fill_bound_evidence_for_low_bound(implied_evidence, be);
        } else {
            unsigned k = improved_low_bounds[implied_evidence.m_j] = bound_evidences.size();
            bound_evidences.push_back(bound_evidence());
            fill_bound_evidence_for_low_bound(implied_evidence, bound_evidences[k]);
        }
    }

    void fill_bound_evidence_for_low_bound(implied_bound_evidence_signature<mpq, numeric_pair<mpq>>& implied_evidence,
                                             bound_evidence & be) {
        be.m_j = implied_evidence.m_j;
        be.m_bound = implied_evidence.m_bound.x;
        be.m_kind = implied_evidence.m_bound.y.is_zero() ? GE : GT;
        for (auto t : implied_evidence.m_evidence) {
            const canonic_left_side & cls = m_vec_of_canonic_left_sides[t.m_i];
            const ul_pair & ul = m_map_of_canonic_left_sides_to_ul_pairs[cls];
            constraint_index witness = t.m_low_bound ? ul.m_low_bound_witness : ul.m_upper_bound_witness;
            lean_assert(is_valid(witness));
            be.m_evidence.emplace_back(t.m_coeff, witness);
        }
    }

    void fill_bound_evidence_for_upper_bound(implied_bound_evidence_signature<mpq, numeric_pair<mpq>>& implied_evidence,
                                             bound_evidence & be) {
        be.m_j = implied_evidence.m_j;
        be.m_bound = implied_evidence.m_bound.x;
        be.m_kind = implied_evidence.m_bound.y.is_zero() ? LE : LT;
        for (auto t : implied_evidence.m_evidence) {
            const canonic_left_side & cls = m_vec_of_canonic_left_sides[t.m_i];
            const ul_pair & ul = m_map_of_canonic_left_sides_to_ul_pairs[cls];
            constraint_index witness = t.m_low_bound ? ul.m_low_bound_witness : ul.m_upper_bound_witness;
            lean_assert(is_valid(witness));
            be.m_evidence.emplace_back(t.m_coeff, witness);
        }
    }
    void process_new_implied_evidence_for_upper_bound(
                                                      implied_bound_evidence_signature<mpq, numeric_pair<mpq>>& implied_evidence, 
        std::vector<bound_evidence> & bound_evidences,
        std::unordered_map<unsigned, unsigned> & improved_upper_bounds) {
        unsigned existing_index;
        if (try_get_val(improved_upper_bounds, implied_evidence.m_j, existing_index)) {
            bound_evidence & be = bound_evidences[existing_index];
            be.m_evidence.clear();
            // we are improving the existent bound improve the existing bound
            fill_bound_evidence_for_upper_bound(implied_evidence, be);
        } else {
            unsigned k = improved_upper_bounds[implied_evidence.m_j] = bound_evidences.size();
            bound_evidences.push_back(bound_evidence());
            fill_bound_evidence_for_upper_bound(implied_evidence, bound_evidences[k]);
        }
    }

    void process_new_implied_evidence(
                                      implied_bound_evidence_signature<mpq, numeric_pair<mpq>>& implied_evidence, // not pushed yet
        std::vector<bound_evidence> & bound_evidences,
        std::unordered_map<unsigned, unsigned> & improved_low_bounds,
        std::unordered_map<unsigned, unsigned> & improved_upper_bounds) {
        lean_assert(implied_evidence.m_evidence.size() > 0);
        if (implied_evidence.m_low_bound)
            process_new_implied_evidence_for_low_bound(implied_evidence, bound_evidences, improved_low_bounds);
        else 
            process_new_implied_evidence_for_upper_bound(implied_evidence, bound_evidences, improved_upper_bounds);
    }
    void process_new_implied_evidences(
                                       std::vector<implied_bound_evidence_signature<mpq, numeric_pair<mpq>>>& evidence_vector,
        std::vector<bound_evidence> & bound_evidences,
        std::unordered_map<unsigned, unsigned> & improved_low_bounds,
        std::unordered_map<unsigned, unsigned> & improved_upper_bounds) {
        for (auto & ibs : evidence_vector)
            process_new_implied_evidence(ibs, bound_evidences, improved_low_bounds, improved_upper_bounds);
    }

    bool propagate_bounds_for_touched_rows_one_time(
                                                    std::vector<bound_evidence> & bound_evidences,
                                                    std::unordered_map<unsigned, unsigned> & improved_low_bounds,
                                                    std::unordered_map<unsigned, unsigned> & improved_upper_bounds) {
        bool found = false;
        std::vector<int> rows_to_check = m_touched_rows.m_index;
        m_touched_rows.clear();

        for (auto i : rows_to_check) {
            std::vector<implied_bound_evidence_signature<mpq, numeric_pair<mpq>>> evidence_vector;
            calculate_implied_bound_evidences(i, evidence_vector);
            found = evidence_vector.size() > 0;
            
            if (get_status() == INFEASIBLE) {
                return false;
            }

            process_new_implied_evidences(evidence_vector, bound_evidences, improved_low_bounds, improved_upper_bounds);
        }
        return found;
    }
    
    // goes over touched rows and tries to induce bounds
    void propagate_bounds_for_touched_rows(std::vector<bound_evidence> & bound_evidences) {
        std::unordered_map<unsigned, unsigned> improved_low_bounds;
        std::unordered_map<unsigned, unsigned> improved_upper_bounds;
        while (propagate_bounds_for_touched_rows_one_time(bound_evidences,
                                                          improved_low_bounds,
                                                          improved_upper_bounds)){};
        m_settings.st().m_num_of_implied_bounds += improved_low_bounds.size() + improved_upper_bounds.size();
    }

    constraint_index add_constraint(const std::vector<std::pair<mpq, var_index>>& left_side, lconstraint_kind kind_par, mpq right_side_par);

    constraint_index add_constraint_for_existing_left_side(const canonic_left_side& cls, lconstraint_kind kind_par, mpq right_side_par);

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

    lp_status solve();

    void get_infeasibility_evidence(std::vector<std::pair<mpq, constraint_index>> & evidence);
    void fill_evidence_from_canonic_left_side(std::vector<std::pair<mpq, constraint_index>> & evidence);

    void get_infeasibility_evidence_for_inf_sign(std::vector<std::pair<mpq, constraint_index>> & evidence,
                                                 const std::vector<std::pair<mpq, unsigned>> & inf_row,
                                                 int inf_sign);



    void get_model(std::unordered_map<var_index, mpq> & variable_values) const;

    std::string get_variable_name(var_index vi) const;

    void print_constraints(std::ostream & out) const ;

    void print_constraint(constraint_index ci, std::ostream & out) const ;

    void print_canonic_left_side(const canonic_left_side & c, std::ostream & out) const ;

    void print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out) const ;

    void print_term(unsigned term_column_index, std::ostream & out) const {
        unsigned i = m_columns_name_term[term_column_index].m_term_index_in_normalized_constraints;
        print_left_side_of_constraint(& (m_normalized_constraints[i].m_origin_constraint), out);
    }

    mpq get_infeasibility_of_solution(std::unordered_map<std::string, mpq> & solution);

    mpq get_infeasibility_of_constraint(const lar_normalized_constraint & norm_constr, std::unordered_map<std::string, mpq> & solution);

    mpq get_canonic_left_side_val(const canonic_left_side & ls, std::unordered_map<std::string, mpq> & solution);

    mpq get_left_side_val(const lar_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const;

    void print_constraint(const lar_base_constraint * c, std::ostream & out) const;
    unsigned get_total_iterations() const { return m_mpq_lar_core_solver.m_r_solver.total_iterations(); }
// see http://research.microsoft.com/projects/z3/smt07.pdf
// This method searches for a feasible solution with as many different values of variables, reverenced in vars, as it can find
// Attention, after a call to this method the non-basic variables don't necesserarly stick to their bounds anymore
    void random_update(unsigned sz, var_index const* vars);
    void try_pivot_fixed_vars_from_basis();
    void fill_var_set_for_random_update(unsigned sz, var_index const * vars, std::vector<unsigned>& column_list);

    const std::vector<std::pair<mpq, var_index>> get_term_coefficients(unsigned j) const {
        lean_assert(is_term(j));
        int i = m_columns_name_term[j].m_term_index_in_normalized_constraints;
        auto const & extended_term_coeffs = m_normalized_constraints[i].m_origin_constraint.get_left_side_coefficients();
        std::vector<std::pair<mpq, var_index>> ret;
        for (unsigned k = 0; k < extended_term_coeffs.size() - 1; k++) {
            ret.push_back(extended_term_coeffs[k]);
        }
        return ret;
    }
    std::vector<unsigned> get_list_of_all_var_indices() const {
        std::vector<unsigned> ret;
        for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_heading.size(); j++)
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
        auto & b = m_mpq_lar_core_solver.m_r_basis;
        b.clear();
        for (auto & t : m_map_of_canonic_left_sides_to_ul_pairs()) {
            if (t.first.size() > 1)
                b.push_back(t.second.m_j);
        }
    }
    std::string create_term_name(unsigned j) {
        std::string name = std::string("_t") + T_to_string(j);
        while (m_var_names_to_var_index.contains(name)) {
            name += "_";
        }
        return name;
    }

    var_index add_term(const std::vector<std::pair<mpq, var_index>> & coeffs,
                       const mpq & v, constraint_index& ci) {
        var_index j = A_r().column_count();
        std::string term_name = create_term_name(j);
        unsigned i = m_normalized_constraints.size();
        var_index jj = add_var(term_name);
        lean_assert(jj == j);
        std::vector<std::pair<mpq, var_index>> term_coeffs = coeffs; // copy coeffs
        term_coeffs.emplace_back(- one_of_type<mpq>(), j);
        ci = add_constraint(term_coeffs, EQ, - v);
        m_columns_name_term[j].m_term_column_index = j;
        m_columns_name_term[j].m_term_index_in_normalized_constraints = i;
        return j;
    }

    void pop_core_solver_params() {
        pop_core_solver_params(1);
    }

    void pop_core_solver_params(unsigned k) {
        A_r().pop(k);
        A_d().pop(k);
    }

    void add_new_var_to_core_fields_r(bool register_in_basis, const numeric_pair<mpq> & val) {
        unsigned j = A_r().column_count();
        A_r().add_column();
        lean_assert(m_mpq_lar_core_solver.m_r_x.size() == j);
        //        lean_assert(m_mpq_lar_core_solver.m_r_low_bounds.size() == j && m_mpq_lar_core_solver.m_r_upper_bounds.size() == j);  // restore later
        m_mpq_lar_core_solver.m_r_x.push_back(val);
        m_mpq_lar_core_solver.m_r_low_bounds.enlarge_by_one();
        m_mpq_lar_core_solver.m_r_upper_bounds.enlarge_by_one();

        lean_assert(m_mpq_lar_core_solver.m_r_heading.size() == j); // as A().column_count() on the entry to the method
        if (register_in_basis) {
            A_r().add_row();
            m_mpq_lar_core_solver.m_r_heading.push_back(m_mpq_lar_core_solver.m_r_basis.size());
            m_mpq_lar_core_solver.m_r_basis.push_back(j);
        }else {
            m_mpq_lar_core_solver.m_r_heading.push_back(- static_cast<int>(m_mpq_lar_core_solver.m_r_nbasis.size()) - 1);
            m_mpq_lar_core_solver.m_r_nbasis.push_back(j);
        }
    }

    void add_new_var_to_core_fields_d(bool register_in_basis) {
        unsigned j = A_d().column_count();
        A_d().add_column();
        lean_assert(m_mpq_lar_core_solver.m_d_x.size() == j);
        //        lean_assert(m_mpq_lar_core_solver.m_d_low_bounds.size() == j && m_mpq_lar_core_solver.m_d_upper_bounds.size() == j);  // restore later
        m_mpq_lar_core_solver.m_d_x.resize(j + 1 ); 
        m_mpq_lar_core_solver.m_d_low_bounds.enlarge_by_one();
        m_mpq_lar_core_solver.m_d_upper_bounds.enlarge_by_one();
        lean_assert(m_mpq_lar_core_solver.m_d_heading.size() == j); // as A().column_count() on the entry to the method
        if (register_in_basis) {
            A_d().add_row();
            m_mpq_lar_core_solver.m_d_heading.push_back(m_mpq_lar_core_solver.m_d_basis.size());
            m_mpq_lar_core_solver.m_d_basis.push_back(j);
        }else {
            m_mpq_lar_core_solver.m_d_heading.push_back(- static_cast<int>(m_mpq_lar_core_solver.m_d_nbasis.size()) - 1);
            m_mpq_lar_core_solver.m_d_nbasis.push_back(j);
        }
    }

    void add_new_var_to_core_fields(bool register_in_basis, const numeric_pair<mpq> & val) {
        lean_assert(A_r().column_count() == A_d().column_count());
        m_mpq_lar_core_solver.m_column_types.push_back(free_column);
        m_touched_columns.resize(m_touched_columns.data_size() + 1);
        if (register_in_basis) {
            m_touched_rows.resize(m_touched_rows.data_size() + 1);
        }
        add_new_var_to_core_fields_r(register_in_basis, val);
        add_new_var_to_core_fields_d(register_in_basis);
    }

    void register_new_var_name(std::string s) {
        lean_assert(!m_var_names_to_var_index.contains(s));
        unsigned j = m_var_names_to_var_index.size();
        m_var_names_to_var_index[s] = j;
        lean_assert(m_columns_name_term.size() == j || m_columns_name_term.size() == j + 1);
        if (m_columns_name_term.size() == j) 
            m_columns_name_term.push_back(s);
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

    bool has_lower_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict);
    
    bool has_upper_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict);
    
    void update_free_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_ind) {
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            m_mpq_lar_core_solver.m_column_types[j] = upper_bound;
            lean_assert(m_mpq_lar_core_solver.m_column_types[j] == upper_bound);
            lean_assert(m_mpq_lar_core_solver.m_r_upper_bounds.size() > j);
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
                m_touched_columns.insert(j);
            }
            set_upper_bound_witness(constr_ind);
            break;
        case GT:
            y_of_bound = 1;
        case GE:
            m_mpq_lar_core_solver.m_column_types[j] = low_bound;
            lean_assert(m_mpq_lar_core_solver.m_r_upper_bounds.size() > j);
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
                m_touched_columns.insert(j);
            }
            set_low_bound_witness(constr_ind);
            break;
        case EQ:
            m_mpq_lar_core_solver.m_column_types[j] = fixed;
            m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            m_touched_columns.insert(j);
            set_upper_bound_witness(constr_ind);
            set_low_bound_witness(constr_ind);
            break;

        default:
            lean_unreachable();
                
        }
    }

    void update_upper_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_mpq_lar_core_solver.m_column_types[j] == upper_bound);
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                if (up < m_mpq_lar_core_solver.m_r_upper_bounds()[j]) {
                    m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
                    set_upper_bound_witness(ci);
                    m_touched_columns.insert(j);
                }
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            m_mpq_lar_core_solver.m_column_types[j] = boxed;
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
                set_low_bound_witness(ci);
                m_touched_columns.insert(j);
                if (low > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j]? boxed : fixed;
                }                     
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    set_low_bound_witness(ci);
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                    m_touched_columns.insert(j);
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }
                break;
            }
            break;

        default:
            lean_unreachable();
                
        }
    }
    
    void update_boxed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_column_types[j] == boxed && m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j]));
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                if (up < m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
                    set_upper_bound_witness(ci);
                }
                m_touched_columns.insert(j);

                if (up < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    if (m_mpq_lar_core_solver.m_r_low_bounds()[j] == m_mpq_lar_core_solver.m_r_upper_bounds()[j])
                        m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }                    
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low > m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
                    m_touched_columns.insert(j);
                    set_low_bound_witness(ci);
                }
                if (low > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else if ( low == m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);                    
                } else {
                    m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }
                m_touched_columns.insert(j);
                
                break;
            }

        default:
            lean_unreachable();
                
        }
    }
    void update_low_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_mpq_lar_core_solver.m_column_types[j] == low_bound);
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
                set_upper_bound_witness(ci);
                m_touched_columns.insert(j);

                if (up < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j]? boxed : fixed;
                }                    
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low > m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
                    m_touched_columns.insert(j);
                    set_low_bound_witness(ci);
                }
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else {
                    m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }
                m_touched_columns.insert(j);
                break;
            }

        default:
            lean_unreachable();
                
        }
    }

    void update_fixed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_column_types[j] == fixed && m_mpq_lar_core_solver.m_r_low_bounds()[j] == m_mpq_lar_core_solver.m_r_upper_bounds()[j]));
        lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_r_low_bounds()[j].y.is_zero() && m_mpq_lar_core_solver.m_r_upper_bounds()[j].y.is_zero()));
        auto v = numeric_pair<mpq>(right_side, mpq(0));
        
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            if (v <= m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                set_upper_bound_witness(ci);
            }                   
            break;
        case LE:
            {
                if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);
                }                   
            }
            break;
        case GT:
            {
                if (v >= m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);
                }
            }
            break;
        case GE:            
            {
                if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);
                }
            }
            break;
        case EQ:
            {
                if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
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
        switch(m_mpq_lar_core_solver.m_column_types[j]) {
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
    }


    numeric_pair<mpq> get_delta_of_touched_nb_column(unsigned j) {
        switch (m_mpq_lar_core_solver.m_column_types[j]) {
        case fixed:
            return m_mpq_lar_core_solver.m_r_low_bounds()[j] - m_mpq_lar_core_solver.m_r_x[j];
        case boxed:
            if (m_mpq_lar_core_solver.m_r_x[j] < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                return m_mpq_lar_core_solver.m_r_low_bounds()[j] - m_mpq_lar_core_solver.m_r_x[j];
            }
            
            if (m_mpq_lar_core_solver.m_r_x[j] > m_mpq_lar_core_solver.m_r_upper_bounds()[j]) {
                return m_mpq_lar_core_solver.m_r_upper_bounds()[j] - m_mpq_lar_core_solver.m_r_x[j];
            }
            return zero_of_type<numeric_pair<mpq>>();
        case low_bound:
            return (m_mpq_lar_core_solver.m_r_x[j] < m_mpq_lar_core_solver.m_r_low_bounds[j])?
                m_mpq_lar_core_solver.m_r_low_bounds()[j] - m_mpq_lar_core_solver.m_r_x[j] : zero_of_type<numeric_pair<mpq>>();
        case upper_bound:
            return (m_mpq_lar_core_solver.m_r_x[j] > m_mpq_lar_core_solver.m_r_upper_bounds()[j])?
                m_mpq_lar_core_solver.m_r_upper_bounds()[j] - m_mpq_lar_core_solver.m_r_x[j] :
                zero_of_type<numeric_pair<mpq>>();

        case free_column:
            return zero_of_type<numeric_pair<mpq>>();
        default:
            lean_assert(false);
            break;
        }
        return zero_of_type<numeric_pair<mpq>>(); // to avoid the compiler warning
    }
    
    void fix_touched_column(unsigned j) {
        if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) { // it is a basic column
            // just mark the row at touched and exit
            m_touched_rows.insert(m_mpq_lar_core_solver.m_r_heading[j]);
            return;
        }
        numeric_pair<mpq> delta = get_delta_of_touched_nb_column(j);

        if (A_r().row_count() != m_column_buffer.data_size())
            m_column_buffer.resize(A_r().row_count());
        else
            m_column_buffer.clear();
        lean_assert(m_column_buffer.size() == 0 && m_column_buffer.is_OK());
        
        m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
        if (delta.is_zero()) {
            for (unsigned i : m_column_buffer.m_index) {
                lean_assert(m_touched_rows.data_size() > i);
                m_touched_rows.insert(i);
            }
        } else {
            m_mpq_lar_core_solver.m_r_x[j] += delta;
            for (unsigned i : m_column_buffer.m_index) {
                unsigned jb = m_mpq_lar_core_solver.m_r_basis[i];
                m_mpq_lar_core_solver.m_r_x[jb] -= delta * m_column_buffer[i];
                lean_assert(m_touched_rows.data_size() > i);
                m_touched_rows.insert(i);
            }
        }
    }

    void find_more_touched_columns() { // todo. can it be optimized during pop() ?
        for (unsigned j : m_mpq_lar_core_solver.m_r_nbasis) {
            if (!m_mpq_lar_core_solver.m_r_solver.non_basis_column_is_set_correctly(j))
                m_touched_columns.insert(j);
        }
    }
    
    
    void fix_touched_columns() {
        lean_assert(x_is_correct());
        find_more_touched_columns();
        for (unsigned j : m_touched_columns.m_index)
            fix_touched_column(j);
        m_touched_columns.clear();
        lean_assert(x_is_correct());
    }


    template <typename K, typename L>
    void add_last_rows_to_lu(lp_primal_core_solver<K,L> & s) {
        auto & f = s.m_factorization;
        if (f != nullptr) {
            auto columns_to_replace = f->get_set_of_columns_to_replace_for_add_last_rows(s.m_basis_heading);
            if (f->m_refactor_counter + columns_to_replace.size() >= 200) {
                delete f;
                f = nullptr;
            } else {
                f->add_last_rows_to_B(s.m_basis_heading, columns_to_replace);
            }
        }
        if (f == nullptr) {

            init_factorization(f, s.m_A, s.m_basis, m_settings);
            if (f->get_status() != LU_status::OK) {
                delete f;
                f = nullptr;
            }
        }
        
    }
    
    bool x_is_correct() const {
        if (m_mpq_lar_core_solver.m_r_x.size() != A_r().column_count()) {
            //            std::cout << "the size is off " << m_r_solver.m_x.size() << ", " << A().column_count() << std::endl;
            return false;
        }
        for (unsigned i = 0; i < A_r().row_count(); i++) {
            numeric_pair<mpq> delta =  A_r().dot_product_with_row(i, m_mpq_lar_core_solver.m_r_x);
            if (!delta.is_zero()) {
                // std::cout << "x is off (";
                // std::cout << "m_b[" << i  << "] = " << m_b[i] << " ";
                // std::cout << "left side = " << A().dot_product_with_row(i, m_r_solver.m_x) << ' ';
                // std::cout << "delta = " << delta << ' ';
                // std::cout << "iters = " << total_iterations() << ")" << std::endl;
                // std::cout << "row " << i << " is off" << std::endl;
                return false;
            }
        }
        return true;;
    
    }

    // returns true even for vars created for canonic_left_sides
    bool var_is_registered(var_index vj) const {
        return  vj < m_vec_of_canonic_left_sides.size();
    }
};
}
