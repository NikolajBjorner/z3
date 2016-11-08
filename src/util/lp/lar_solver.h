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
    lp_settings m_settings;
    // end of fields used in m_mpq_lar_core_solver
    
    stacked_value<lp_status> m_status = UNKNOWN;
    stacked_map<std::string, var_index> m_var_names_to_var_index;
    std::vector<std::string> m_column_names;
    // for each column j its canonic_left_side can be found as m_vec_of_canonic_left_sides[j] 
    stacked_map<canonic_left_side, ul_pair, hash_and_equal_of_canonic_left_side_struct, hash_and_equal_of_canonic_left_side_struct> m_map_of_canonic_left_sides_to_ul_pairs;
    stacked_vector<lar_normalized_constraint> m_normalized_constraints;
    stacked_vector<canonic_left_side> m_vec_of_canonic_left_sides;
    // the set of column indices j such that m_x[j] does not satisfy one of its bounds
    indexed_vector<unsigned> m_touched_columns;
    indexed_vector<unsigned> m_touched_rows;
    lar_core_solver<mpq, numeric_pair<mpq>> m_mpq_lar_core_solver;
    stacked_value<canonic_left_side> m_infeasible_canonic_left_side; // such can be found at the initialization step
    stacked_vector<lar_term> m_terms;
    const var_index m_terms_start_index = 1000000;
    indexed_vector<mpq> m_column_buffer;
    
    ////////////////// methods ////////////////////////////////
    static_matrix<mpq, numeric_pair<mpq>> & A() { return m_mpq_lar_core_solver.m_A;}
    static_matrix<mpq, numeric_pair<mpq>> const & A() const { return m_mpq_lar_core_solver.m_A;}
    
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
    
    bool try_to_set_fixed(column_info<mpq> & ci);

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


    lar_solver() : m_mpq_lar_core_solver(
                                         m_settings,
                                         *this
                                         ) {}

    virtual ~lar_solver(){}

    bool all_constrained_variables_are_registered(const std::vector<std::pair<mpq, var_index>>& left_side);

    var_index add_var(std::string s);

    numeric_pair<mpq> const& get_value(var_index vi) const { return m_mpq_lar_core_solver.m_x[vi]; }

    bool is_term(unsigned j) const {
        return j >= m_terms_start_index && j - m_terms_start_index < m_terms.size();
    }

    unsigned adjust_term_index(unsigned j) const {
        lean_assert(is_term(j));
        return j - m_terms_start_index;
    }
    
    constraint_index add_var_bound(var_index j, lconstraint_kind kind, const mpq & right_side)  {
        if (j < A().column_count()) { // j is a var
            const canonic_left_side& cls = m_vec_of_canonic_left_sides[j];
            return add_constraint(cls, kind, right_side);
        }
        // it is a term
        return add_constraint(m_terms()[adjust_term_index(j)].m_coeffs, kind, right_side);
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
        iterator_on_pivot_row<mpq> it(m_mpq_lar_core_solver.get_pivot_row(), m_mpq_lar_core_solver.m_basis[row_index]); 
        bound_analyzer_on_row<mpq, numeric_pair<mpq>> ra_pos(it,
                                                             m_mpq_lar_core_solver.m_low_bounds(),
                                                             m_mpq_lar_core_solver.m_upper_bounds(),
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

    void propagate_bound(var_index j, std::vector<bound_evidence> & bound_evidences, 
        std::unordered_map<unsigned, unsigned> & improved_low_bounds, 
        std::unordered_map<unsigned, unsigned> & improved_upper_bounds) {
        m_mpq_lar_core_solver.m_primal_solver.solve_Bd(j);
        for (unsigned i = 0; i < m_mpq_lar_core_solver.m_primal_solver.m_ed.m_index.size();i++) {
            std::vector<implied_bound_evidence_signature<mpq, numeric_pair<mpq>>> evidence_vector;
            calculate_implied_bound_evidences(m_mpq_lar_core_solver.m_primal_solver.m_ed.m_index[i], evidence_vector);
            process_new_implied_evidences(evidence_vector, bound_evidences, improved_low_bounds, improved_upper_bounds);
        }
#if LEAN_DEBUG
        for (auto & be: bound_evidences) {
            // print_bound_evidence(be);
            bound_evidence_is_correct(be);
        }
#endif

    }

    bool propagate_bounds_for_touched_rows_one_time(
                                                    std::vector<bound_evidence> & bound_evidences,
                                                    std::unordered_map<unsigned, unsigned> & improved_low_bounds,
                                                    std::unordered_map<unsigned, unsigned> & improved_upper_bounds) {
        bool found = false;
        std::vector<unsigned> rows_to_check;
        while (m_touched_rows.m_index.size() > 0) {
            unsigned i = m_touched_rows.m_index.back();
            rows_to_check.push_back(i);
            m_touched_rows.m_index.pop_back();
            m_touched_rows.m_data[i] = 0;
        }

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
    
    
    constraint_index add_var_bound_with_bound_propagation(var_index j, lconstraint_kind kind, mpq right_side, std::vector<bound_evidence> & bound_evidences)  {
        std::unordered_map<unsigned, unsigned> improved_low_bounds; // serves as a guard
        std::unordered_map<unsigned, unsigned> improved_upper_bounds; // serves as a guard
        if (j < A().column_count()) { // j is a var
            constraint_index ret = add_var_bound(j, kind, right_side);
            propagate_bound(j, bound_evidences, improved_low_bounds, improved_upper_bounds);
            return ret;
        }
        // j is a term
        return add_constraint(m_terms()[adjust_term_index(j)].m_coeffs, kind, right_side);
    }

    constraint_index add_constraint(const std::vector<std::pair<mpq, var_index>>& left_side, lconstraint_kind kind_par, mpq right_side_par);
    constraint_index add_constraint(const canonic_left_side& cls, lconstraint_kind kind_par, mpq right_side_par);

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

    void update_delta(mpq& delta, numeric_pair<mpq> const& l, numeric_pair<mpq> const& u) const;

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
    unsigned get_total_iterations() const { return m_mpq_lar_core_solver.m_primal_solver.total_iterations(); }
// see http://research.microsoft.com/projects/z3/smt07.pdf
// This method searches for a feasible solution with as many different values of variables, reverenced in vars, as it can find
// Attention, after a call to this method the non-basic variables don't necesserarly stick to their bounds anymore
    void random_update(unsigned sz, var_index const* vars);
    void try_pivot_fixed_vars_from_basis();
    void fill_var_set_for_random_update(unsigned sz, var_index const * vars, std::vector<unsigned>& column_list);
    
    std::vector<unsigned> get_list_of_all_var_indices() const {
        std::vector<unsigned> ret;
        for (unsigned j = 0; j < m_mpq_lar_core_solver.m_heading.size(); j++)
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
        auto & b = m_mpq_lar_core_solver.m_basis;
        b.clear();
        for (auto & t : m_map_of_canonic_left_sides_to_ul_pairs()) {
            if (t.first.size() > 1)
                b.push_back(t.second.m_j);
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
        return m_settings.presolve_with_double_solver_for_lar
            && A().row_count() > 0; // todo, add more conditions
    }

    bool low_bound_is_set(unsigned j) const {
        switch (m_mpq_lar_core_solver.m_column_types[j]) {
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
        switch (m_mpq_lar_core_solver.m_column_types[j]) {
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
        A().pop(k);
     }

    void add_new_var_to_core_fields(bool register_in_basis, numeric_pair<mpq> val) {
        unsigned i = A().column_count();
        A().add_column();
        lean_assert(m_mpq_lar_core_solver.m_x.size() == i);
        lean_assert(m_mpq_lar_core_solver.m_column_types.size() == i);
        m_mpq_lar_core_solver.m_column_types.push_back(free_column);
        lean_assert(m_mpq_lar_core_solver.m_low_bounds.size() == i && m_mpq_lar_core_solver.m_upper_bounds.size() == i);
        // we need to insert some value, does not matter which
        m_mpq_lar_core_solver.m_low_bounds.push_back(zero_of_type<numeric_pair<mpq>>());
        m_mpq_lar_core_solver.m_upper_bounds.push_back(zero_of_type<numeric_pair<mpq>>());
        m_mpq_lar_core_solver.m_x.push_back(val);
        m_touched_columns.resize(i + 1);

        lean_assert(m_mpq_lar_core_solver.m_heading.size() == i); // as A().column_count() on the entry to the method
        if (register_in_basis) {
            A().add_row();
            m_mpq_lar_core_solver.m_heading.push_back(m_mpq_lar_core_solver.m_basis.size());
            m_mpq_lar_core_solver.m_basis.push_back(i);
            m_touched_rows.resize(A().row_count());
        }else {
            m_mpq_lar_core_solver.m_heading.push_back(- static_cast<int>(m_mpq_lar_core_solver.m_nbasis.size()) - 1);
            m_mpq_lar_core_solver.m_nbasis.push_back(i);
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
            lean_assert(m_mpq_lar_core_solver.m_upper_bounds.size() > j);
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                m_mpq_lar_core_solver.m_upper_bounds[j] = up;
                m_touched_columns.set_value_as_in_dictionary(j);
            }
            set_upper_bound_witness(constr_ind);
            break;
        case GT:
            y_of_bound = 1;
        case GE:
            m_mpq_lar_core_solver.m_column_types[j] = low_bound;
            lean_assert(m_mpq_lar_core_solver.m_upper_bounds.size() > j);
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                m_mpq_lar_core_solver.m_low_bounds[j] = low;
                m_touched_columns.set_value_as_in_dictionary(j);
            }
            set_low_bound_witness(constr_ind);
            break;
        case EQ:
            m_mpq_lar_core_solver.m_column_types[j] = fixed;
            m_mpq_lar_core_solver.m_low_bounds[j] = m_mpq_lar_core_solver.m_upper_bounds[j] = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            m_touched_columns.set_value_as_in_dictionary(j);
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
                if (up < m_mpq_lar_core_solver.m_upper_bounds()[j]) {
                    m_mpq_lar_core_solver.m_upper_bounds[j] = up;
                    set_upper_bound_witness(ci);
                    m_touched_columns.set_value_as_in_dictionary(j);
                }
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            m_mpq_lar_core_solver.m_column_types[j] = boxed;
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                m_mpq_lar_core_solver.m_low_bounds[j] = low;
                set_low_bound_witness(ci);
                m_touched_columns.set_value_as_in_dictionary(j);
                if (low > m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_low_bounds()[j] < m_mpq_lar_core_solver.m_upper_bounds()[j]? boxed : fixed;
                }                     
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v > m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    set_low_bound_witness(ci);
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_mpq_lar_core_solver.m_low_bounds[j] = m_mpq_lar_core_solver.m_upper_bounds[j] = v;
                    m_touched_columns.set_value_as_in_dictionary(j);
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
        lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_column_types[j] == boxed && m_mpq_lar_core_solver.m_low_bounds()[j] < m_mpq_lar_core_solver.m_upper_bounds()[j]));
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
        case LE:
            {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                if (up < m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_mpq_lar_core_solver.m_upper_bounds[j] = up;
                    set_upper_bound_witness(ci);
                }
                m_touched_columns.set_value_as_in_dictionary(j);

                if (up < m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    if (m_mpq_lar_core_solver.m_low_bounds()[j] == m_mpq_lar_core_solver.m_upper_bounds()[j])
                        m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }                    
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low > m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_mpq_lar_core_solver.m_low_bounds[j] = low;
                    m_touched_columns.set_value_as_in_dictionary(j);
                    set_low_bound_witness(ci);
                }
                if (low > m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else if ( low == m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v < m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else if (v > m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);                    
                } else {
                    m_mpq_lar_core_solver.m_low_bounds[j] = m_mpq_lar_core_solver.m_upper_bounds[j] = v;
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }
                m_touched_columns.set_value_as_in_dictionary(j);
                
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
                m_mpq_lar_core_solver.m_upper_bounds[j] = up;
                set_upper_bound_witness(ci);
                m_touched_columns.set_value_as_in_dictionary(j);

                if (up < m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                } else {
                    m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_low_bounds()[j] < m_mpq_lar_core_solver.m_upper_bounds()[j]? boxed : fixed;
                }                    
            }
            break;
        case GT:
            y_of_bound = 1;
        case GE:            
            {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low > m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_mpq_lar_core_solver.m_low_bounds[j] = low;
                    m_touched_columns.set_value_as_in_dictionary(j);
                    set_low_bound_witness(ci);
                }
            }
            break;
        case EQ:
            {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v < m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else {
                    m_mpq_lar_core_solver.m_low_bounds[j] = m_mpq_lar_core_solver.m_upper_bounds[j] = v;
                    set_low_bound_witness(ci);
                    set_upper_bound_witness(ci);
                    m_mpq_lar_core_solver.m_column_types[j] = fixed;
                }
                m_touched_columns.set_value_as_in_dictionary(j);
                break;
            }

        default:
            lean_unreachable();
                
        }
    }

    void update_fixed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
        lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_column_types[j] == fixed && m_mpq_lar_core_solver.m_low_bounds()[j] == m_mpq_lar_core_solver.m_upper_bounds()[j]));
        lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_low_bounds()[j].y.is_zero() && m_mpq_lar_core_solver.m_upper_bounds()[j].y.is_zero()));
        auto v = numeric_pair<mpq>(right_side, mpq(0));
        
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            if (v <= m_mpq_lar_core_solver.m_low_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                set_upper_bound_witness(ci);
            }                   
            break;
        case LE:
            {
                if (v < m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);
                }                   
            }
            break;
        case GT:
            {
                if (v >= m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);
                }
            }
            break;
        case GE:            
            {
                if (v > m_mpq_lar_core_solver.m_upper_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_low_bound_witness(ci);
                }
            }
            break;
        case EQ:
            {
                if (v < m_mpq_lar_core_solver.m_low_bounds[j]) {
                    m_status = INFEASIBLE;
                    m_infeasible_canonic_left_side = m_normalized_constraints()[ci].m_canonic_left_side;
                    set_upper_bound_witness(ci);                    
                } else if (v > m_mpq_lar_core_solver.m_upper_bounds[j]) {
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


    void substitute_terms(const mpq & mult, const std::vector<std::pair<mpq, var_index>>& left_side_with_terms,std::vector<std::pair<mpq, var_index>> &left_side, mpq & right_side) const {
        for (auto & t : left_side_with_terms) {
            if (t.second < m_terms_start_index) {
                lean_assert(t.second < A().column_count());
                left_side.push_back(std::pair<mpq, var_index>(mult * t.first, t.second));
            } else {
                const lar_term & term = m_terms[adjust_term_index(t.second)];
                substitute_terms(mult * t.first, term.m_coeffs, left_side, right_side);
                right_side -= mult * term.m_v;
            }
        }
    }


    numeric_pair<mpq> get_delta_of_touched_nb_column(unsigned j) {
        switch (m_mpq_lar_core_solver.m_column_types[j]) {
        case fixed:
        case boxed:
            if (m_mpq_lar_core_solver.m_x[j] <= m_mpq_lar_core_solver.m_low_bounds[j]) { // the equality case will work just fine
                return m_mpq_lar_core_solver.m_low_bounds()[j] - m_mpq_lar_core_solver.m_x[j];
            }
            
            if (m_mpq_lar_core_solver.m_x[j] >= m_mpq_lar_core_solver.m_upper_bounds()[j]) {
                return m_mpq_lar_core_solver.m_upper_bounds()[j] - m_mpq_lar_core_solver.m_x[j];
            }
            return my_random() % 2 == 0?  m_mpq_lar_core_solver.m_upper_bounds()[j] - m_mpq_lar_core_solver.m_x[j] : m_mpq_lar_core_solver.m_low_bounds()[j] - m_mpq_lar_core_solver.m_x[j];
        case low_bound:
            return m_mpq_lar_core_solver.m_low_bounds()[j] - m_mpq_lar_core_solver.m_x[j];
        case upper_bound:
            return m_mpq_lar_core_solver.m_upper_bounds()[j] - m_mpq_lar_core_solver.m_x[j];
        case free_column:
            return zero_of_type<numeric_pair<mpq>>();
        default:
            lean_assert(false);
            break;
        }
        return zero_of_type<numeric_pair<mpq>>(); // to avoid the compiler warning
    }
    
    void fix_touched_column(unsigned j) {
        if (m_mpq_lar_core_solver.m_heading[j] >= 0) { // it is a basic column
            // just mark the row at touched and exit
            m_touched_rows.set_value_as_in_dictionary(m_mpq_lar_core_solver.m_heading[j]);
            return;
        }
        numeric_pair<mpq> delta = get_delta_of_touched_nb_column(j);
        if (delta.is_zero())
            return;

        if (A().row_count() != m_column_buffer.data_size())
            m_column_buffer.resize(A().row_count());
        else
            m_column_buffer.clear();
        m_mpq_lar_core_solver.m_primal_solver.solve_Bd(j, m_column_buffer);
        m_mpq_lar_core_solver.m_x[j] += delta;
        for (unsigned i : m_column_buffer.m_index) {
            unsigned jb = m_mpq_lar_core_solver.m_basis[i];
            m_mpq_lar_core_solver.m_x[jb] -= delta * m_column_buffer[i];
            lean_assert(m_touched_rows.data_size() > i);
            m_touched_rows.set_value_as_in_dictionary(i);
        }
    }

    void find_more_touched_columns() { // todo. can it be optimized during pop() ?
        for (unsigned j : m_mpq_lar_core_solver.m_nbasis) {
            if (!m_mpq_lar_core_solver.m_primal_solver.non_basis_column_is_set_correctly(j))
                m_touched_columns.set_value_as_in_dictionary(j);
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

    bool x_is_correct() const {
        if (m_mpq_lar_core_solver.m_x.size() != A().column_count()) {
            //            std::cout << "the size is off " << m_mpq_lar_core_solver.m_x.size() << ", " << A().column_count() << std::endl;
            return false;
        }
        for (unsigned i = 0; i < A().row_count(); i++) {
            numeric_pair<mpq> delta =  A().dot_product_with_row(i, m_mpq_lar_core_solver.m_x);
            if (!delta.is_zero()) {
                // std::cout << "x is off (";
                // std::cout << "m_b[" << i  << "] = " << m_b[i] << " ";
                // std::cout << "left side = " << A().dot_product_with_row(i, m_mpq_lar_core_solver.m_x) << ' ';
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
        if (vj >= m_terms_start_index) {
            if (vj - m_terms_start_index >= m_terms.size())
                return false;
        } else if ( vj >= m_vec_of_canonic_left_sides.size()) {
            return false;
        }
        return true;
    }
};
}
