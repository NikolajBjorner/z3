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
#include "util/lp/lar_solution_signature.h"
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
    std::vector<double> m_d_right_sides_dummy;
    std::vector<double> m_d_costs_dummy;
public:
    stacked_vector<column_type> m_column_types;
    // r - solver fields, for rational numbers
    std::vector<numeric_pair<mpq>> m_r_x; // the solution
    stacked_vector<numeric_pair<mpq>> m_r_low_bounds;
    stacked_vector<numeric_pair<mpq>> m_r_upper_bounds;
    static_matrix<mpq, numeric_pair<mpq>> m_r_A;
    stacked_vector<unsigned> m_r_pushed_basis;
    std::vector<unsigned> m_r_basis;
    std::vector<unsigned> m_r_nbasis;
    std::vector<int> m_r_heading;
    stacked_vector<unsigned> m_r_columns_nz;
    stacked_vector<unsigned> m_r_rows_nz;
    
    // d - solver fields, for doubles
    std::vector<double> m_d_x; // the solution in doubles
    stacked_vector<double> m_d_low_bounds;
    stacked_vector<double> m_d_upper_bounds;
    static_matrix<double, double> m_d_A;
    stacked_vector<unsigned> m_d_pushed_basis;
    std::vector<unsigned> m_d_basis;
    std::vector<unsigned> m_d_nbasis;
    std::vector<int> m_d_heading;


    lp_primal_core_solver<T, X> m_r_solver; // solver in rational numbers

    lp_primal_core_solver<double, double> m_d_solver; // solver in doubles
    
    lar_core_solver(
                    lp_settings & settings,
                    const column_namer & column_names
                    );

    lp_settings & settings() { return m_r_solver.m_settings;}
    const lp_settings & settings() const { return m_r_solver.m_settings;}
    
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

    void prefix_r();

    void prefix_d();

    unsigned m_m() const {
        return m_r_A.row_count();
    }

    unsigned m_n() const {
        return m_r_A.column_count();
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

    const indexed_vector<T> & get_pivot_row() const {
        return m_r_solver.m_pivot_row;
    }
    
    void fill_not_improvable_zero_sum();

    void pop_basis_parametric(unsigned k,
                              stacked_vector<unsigned> & pushed_basis,
                              std::vector<unsigned> & basis,
                              std::vector<unsigned> & nbasis,
                              std::vector<int> & heading,
                              unsigned n)  {
        pushed_basis.pop(k);
        heading.clear();
        heading.resize(n, -10000000);
        basis.clear();
        for (unsigned i = 0; i < pushed_basis.size(); i++ ) {
            unsigned j = pushed_basis[i];
            heading[j] = i;
            basis.push_back(j);
        }
        
        nbasis.clear();
        for (unsigned j = 0; j < heading.size(); j++) {
            if (m_column_types[j] == fixed) continue;
            int & pos = heading[j]; // we are going to change it!
            if (pos < 0 ) { // j is in nbasis
                pos = -1 - static_cast<int>(nbasis.size());
                nbasis.push_back(j);
            }
        }
    }
    
    void pop_basis(unsigned k) {
        pop_basis_parametric(k, m_r_pushed_basis, m_r_basis, m_r_nbasis, m_r_heading, m_r_A.column_count());
        //        lean_assert(m_r_A.column_count() == m_d_A.column_count());
        pop_basis_parametric(k, m_d_pushed_basis, m_d_basis, m_d_nbasis, m_d_heading, m_d_A.column_count());
    }

    void push() {
        m_column_types.push();
        // rational
        m_r_A.push();
        m_r_low_bounds.push();
        m_r_upper_bounds.push();
        push_vector(m_r_pushed_basis, m_r_basis);
        push_vector(m_r_columns_nz, m_r_solver.m_columns_nz);
        push_vector(m_r_rows_nz, m_r_solver.m_rows_nz);
        
        // doubles
        m_d_A.push();
        m_d_low_bounds.push();
        m_d_upper_bounds.push();
        push_vector(m_d_pushed_basis, m_d_basis);
    }

    template <typename K> 
    void push_vector(stacked_vector<K> & pushed_vector, const std::vector<K> & vector) {
        lean_assert(pushed_vector.size() <= vector.size());
        for (unsigned i = 0; i < vector.size();i++) {
            if (i == pushed_vector.size()) {
                pushed_vector.push_back(vector[i]);
            } else {
                pushed_vector[i] = vector[i];
            }
        }
        pushed_vector.push();
    }

    void pop_markowitz_counts(unsigned k) {
        m_r_columns_nz.pop(k);
        m_r_rows_nz.pop(k);
        m_r_solver.m_columns_nz.resize(m_r_columns_nz.size());
        m_r_solver.m_rows_nz.resize(m_r_rows_nz.size());
        for (unsigned i = 0; i < m_r_columns_nz.size(); i++)
            m_r_solver.m_columns_nz[i] = m_r_columns_nz[i];
        for (unsigned i = 0; i < m_r_rows_nz.size(); i++)
            m_r_solver.m_rows_nz[i] = m_r_rows_nz[i];
    }
    
    void pop(unsigned k) {
        // rationals
        m_r_A.pop(k);
        m_r_low_bounds.pop(k);
        m_r_upper_bounds.pop(k);
        m_column_types.pop(k);
        if (m_r_solver.m_factorization != nullptr) {
            delete m_r_solver.m_factorization;
            m_r_solver.m_factorization = nullptr;
        }
        m_r_x.resize(m_r_A.column_count());
        pop_markowitz_counts(k);
        // doubles
        m_d_A.pop(k);
        m_d_low_bounds.pop(k);
        m_d_upper_bounds.pop(k);
        if (m_d_solver.m_factorization != nullptr) {
            delete m_d_solver.m_factorization;
            m_d_solver.m_factorization = nullptr;
        }
        m_d_x.resize(m_d_A.column_count());
        pop_basis(k);

        lean_assert(m_r_solver.basis_heading_is_correct());
        lean_assert(m_d_solver.basis_heading_is_correct());

    }

    bool need_to_presolve_with_double_solver() const {
        return settings().presolve_with_double_solver_for_lar  && m_r_A.row_count() > 0;
    }

    template <typename L>
    bool is_zero_vector(const std::vector<L> & b) {
        for (const L & m: b)
            if (!is_zero(m)) return false;
        return true;
    }

    template <typename L, typename K>
    void prepare_solver_x_with_signature(const lar_solution_signature & signature, lp_primal_core_solver<L,K> & s) {
        for (auto &t : signature) {
            unsigned j = t.first;
            lean_assert(m_r_heading[j] < 0);
            auto pos_type = t.second;
            switch (pos_type) {
            case at_low_bound:
                s.m_x[j] = s.m_low_bounds[j];
                break;
            case at_fixed:
            case at_upper_bound:
                s.m_x[j] = s.m_upper_bounds[j];
                break;
            case free_of_bounds: {
                s.m_x[j] = zero_of_type<K>();
                continue;
            }
            default:
                lean_unreachable();
            }
        }

        lean_assert(is_zero_vector(s.m_b));
        s.solve_Ax_eq_b();
    }


    template <typename L, typename K> 
    void catch_up_in_lu(const std::vector<unsigned> & trace_of_basis_change, lp_primal_core_solver<L,K> & cs) {
        if (cs.m_factorization->m_refactor_counter + trace_of_basis_change.size() >= 200) {
            for (unsigned i = 0; i < trace_of_basis_change.size(); i+= 2) {
                //  entering basis_delta[i], leaving nbasis_delta[i]
                unsigned entering = trace_of_basis_change[i];
                unsigned leaving = trace_of_basis_change[i+1];
                cs.change_basis_unconditionally(entering, leaving);
            }
            if (cs.m_factorization != nullptr)
                delete cs.m_factorization;
            cs.m_factorization = nullptr;
        } else {
            indexed_vector<L> w(cs.m_A.row_count());
            auto * l = cs.m_factorization;
            lean_assert(l->get_status() == LU_status::OK);
            bool replace = true;
            for (unsigned i = 0; i < trace_of_basis_change.size(); i+= 2) {
                //  entering basis_delta[i], leaving nbasis_delta[i]
                unsigned entering = trace_of_basis_change[i];
                unsigned leaving = trace_of_basis_change[i+1];
                lean_assert(cs.m_basis_heading[entering] < 0);
                lean_assert(cs.m_basis_heading[leaving] >= 0);
                if (replace) {
                    l->prepare_entering(entering, w); // to init vector w
                    l->replace_column(zero_of_type<L>(), w, cs.m_basis_heading[leaving]);
                }
                if (l->get_status() != LU_status::OK) {
                    replace = false; // will not call replace_column anymore
                    if (cs.m_factorization != nullptr)
                        delete cs.m_factorization;
                    cs.m_factorization = nullptr;
                }
                cs.change_basis_unconditionally(entering, leaving);
            }
        }
        if (cs.m_factorization == nullptr) {
            if (numeric_traits<L>::precise())
                init_factorization(cs.m_factorization, cs.m_A, cs.m_basis, settings());
        }
    }

    
    void solve_on_signature(const lar_solution_signature & signature, const std::vector<unsigned> & changes_of_basis) {
        if (m_r_solver.m_factorization == nullptr) {
            for (unsigned j = 0; j < changes_of_basis.size(); j+=2) {
                unsigned entering = changes_of_basis[j];
                unsigned leaving = changes_of_basis[j + 1];
                m_r_solver.change_basis_unconditionally(entering, leaving);
                init_factorization(m_r_solver.m_factorization, m_r_A, m_r_basis, settings());
            }
        } else {
            catch_up_in_lu(changes_of_basis, m_r_solver);
        }
            
        prepare_solver_x_with_signature(signature, m_r_solver);
        m_r_solver.start_tracing_basis_changes();
        m_r_solver.find_feasible_solution();
        // and now catch up in the double solver
        lean_assert(m_r_solver.total_iterations() >= m_r_solver.m_trace_of_basis_change_vector.size() /2);
        //        std::cout << "r solver makes " << m_r_solver.total_iterations() << " steps, status " <<
        //  lp_status_to_string(m_r_solver.get_status());
        // if (m_r_solver.current_x_is_feasible()) std::cout << " feas ";
        // else std::cout << " inf ";
        //std::cout<< std::endl; 
            
        catch_up_in_lu(m_r_solver.m_trace_of_basis_change_vector, m_d_solver);
    }

    void create_double_matrix(static_matrix<double, double> & A) {
        for (unsigned i = 0; i < m_r_A.row_count(); i++) {
            auto & row = m_r_A.m_rows[i];
            for (row_cell<mpq> & c : row) {
                A.set(i, c.m_j, c.get_val().get_double());
            }
        }
    }

    void fill_basis_d(
                      std::vector<unsigned>& basis_d,
                      std::vector<int>& heading_d,
                      std::vector<unsigned>& nbasis_d){
        basis_d = m_r_basis;
        heading_d = m_r_heading;
        nbasis_d = m_r_nbasis;
    }

    template <typename L, typename K>
    void extract_signature_from_lp_core_solver(const lp_primal_core_solver<L, K> & solver, lar_solution_signature & signature) {
        signature.clear();
        lean_assert(signature.size() == 0);
        for (unsigned j = 0; j < solver.m_basis_heading.size(); j++) {
            if (solver.m_basis_heading[j] < 0)
                signature[j] = solver.get_non_basic_column_value_position(j);
        }
    }

    void get_bounds_for_double_solver(std::vector<double> & low_bounds, std::vector<double> & upper_bounds) {
        lean_assert(m_r_solver.A_mult_x_is_off() == false);
        lean_assert(low_bounds.size() == upper_bounds.size() && upper_bounds.size() == m_r_A.column_count());
        mpq delta = find_delta_for_strict_boxed_bounds();
        for (unsigned j = 0; j < low_bounds.size(); j++) {
            if (low_bound_is_set(j)) {
                auto & lb = m_r_solver.m_low_bounds[j];
                low_bounds[j] = (lb.x + delta * lb.y).get_double();
            }
            if (upper_bound_is_set(j)) {
                auto & ub = m_r_solver.m_upper_bounds[j];
                upper_bounds[j] = (ub.x + delta * ub.y).get_double();
                lean_assert(!low_bound_is_set(j) || (upper_bounds[j] >= low_bounds[j]));
            }
        }
    }

    void scale_problem_for_doubles(
                        static_matrix<double, double>& A,        
                        std::vector<double> & low_bounds,
                        std::vector<double> & upper_bounds) {
        std::vector<double> column_scale_vector;
        std::vector<double> right_side_vector(A.column_count());
        settings().reps_in_scaler = 5;
        scaler<double, double > scaler(right_side_vector,
                                       A,
                                       settings().scaling_minimum,
                                       settings().scaling_maximum,
                                       column_scale_vector,
                                       settings());
        if (! scaler.scale()) {
            // the scale did not succeed, unscaling
            A.clear();
            create_double_matrix(A);
            std::cout << "scaler failed\n";
        } else {
            for (unsigned j = 0; j < A.column_count(); j++) {
                if (m_r_solver.column_has_upper_bound(j)) {
                    upper_bounds[j] /= column_scale_vector[j];
                }
                if (m_r_solver.column_has_low_bound(j)) {
                    low_bounds[j] /= column_scale_vector[j];
                }
            }
        }
        
    }
    // returns the trace of basis changes
    std::vector<unsigned> find_solution_signature_with_doubles(lar_solution_signature & signature) {
        if (m_d_solver.m_factorization == nullptr || m_d_solver.m_factorization->get_status() != LU_status::OK) {
            std::vector<unsigned> ret;
            return ret;
        }
        std::vector<double>& low_bounds = m_d_solver.m_low_bounds;
        std::vector<double>& upper_bounds = m_d_solver.m_upper_bounds;
        get_bounds_for_double_solver(low_bounds, upper_bounds);

        std::vector<int>  heading_d;
        std::vector<unsigned> basis_d, nbasis_d;
        fill_basis_d(basis_d, heading_d, nbasis_d);
        //        scale_problem_for_doubles(A, low_bounds, upper_bounds);
        //        std::vector<double> costs(A.column_count());
        extract_signature_from_lp_core_solver(m_r_solver, signature);
        prepare_solver_x_with_signature(signature, m_d_solver);
        m_d_solver.start_tracing_basis_changes();
        m_d_solver.find_feasible_solution();
        // std:: cout << "d solver made " <<  m_d_solver.total_iterations() << " , status " << lp_status_to_string(m_d_solver.m_status);
        // if (m_d_solver.current_x_is_feasible()) std::cout << " feas ";
        // else std::cout << " inf ";
        // std::cout<< std::endl; 

        
        extract_signature_from_lp_core_solver(m_d_solver, signature);
        return m_d_solver.m_trace_of_basis_change_vector;
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

    void update_delta(mpq& delta, numeric_pair<mpq> const& l, numeric_pair<mpq> const& u) const {
        lean_assert(l <= u);
        if (l.x < u.x && l.y > u.y) {
            mpq delta1 = (u.x - l.x) / (l.y - u.y);
            if (delta1 < delta) {
                delta = delta1;
            }
        }
        lean_assert(l.x + delta * l.y <= u.x + delta * u.y);
    }


    mpq find_delta_for_strict_boxed_bounds() const{
        mpq delta = numeric_traits<mpq>::one();
        for (unsigned j = 0; j < m_r_A.column_count(); j++ ) {
            if (m_column_types[j] != boxed)
                continue;
            update_delta(delta, m_r_low_bounds[j], m_r_upper_bounds[j]);

        }
        return delta;
    }

    
    mpq find_delta_for_strict_bounds() const{
        mpq delta = numeric_traits<mpq>::one();
        for (unsigned j = 0; j < m_r_A.column_count(); j++ ) {
            if (low_bound_is_set(j))
                update_delta(delta, m_r_low_bounds[j], m_r_x[j]);
            if (upper_bound_is_set(j))
                update_delta(delta, m_r_x[j], m_r_upper_bounds[j]);
        }
        return delta;
    }

    void init_column_row_nz_for_r_solver() {
        lean_assert(m_r_A.column_count() == m_r_solver.m_columns_nz.size());
        lean_assert(m_r_A.row_count() == m_r_solver.m_rows_nz.size());
        for (unsigned i = 0; i < m_r_A.column_count(); i++) {
            if (m_r_solver.m_columns_nz[i] == 0)
                m_r_solver.m_columns_nz[i] = m_r_solver.m_A.m_columns[i].size();
        }
        for (unsigned i = 0; i < m_r_A.row_count(); i++) {
         if (m_r_solver.m_rows_nz[i] == 0)
            m_r_solver.m_rows_nz[i] = m_r_A.m_rows[i].size();
        }
    }
};
}
