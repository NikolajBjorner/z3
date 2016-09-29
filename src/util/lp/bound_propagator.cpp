/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/bound_propagator.h"
#include "util/lp/lar_solver.h"
namespace lean {
bound_propagator::bound_propagator(unsigned row_index, lar_solver & solver, std::vector<bound_evidence> & bound_evidences) : m_row_index(row_index), m_solver(solver), m_bound_evidences(bound_evidences), m_core_solver(solver.m_mpq_lar_core_solver) {}

void bound_propagator::propagate() {
        m_core_solver.calculate_pivot_row(m_row_index);
                // We have the equality, sum by j of pivot_row[j]*x[j] + x[basis[j]] = 0
        // We try to pin a var by pushing the total of the partial sum down, denoting the variable of this process by _minus.
        // In the same loop trying to pin a var by pushing the partial sum up, denoting it by _plus
        int cand_minus = -1;  // the variable pinned from above
        unsigned n_minus = 0; // the number of terms active, limiting from above found so far
        numeric_pair<mpq> bound_minus = numeric_pair<mpq>(0, 0);
        bool interested_in_minus = true; // the partial sum for min, seen so far
        int cand_plus = -1;
        unsigned n_plus = 0; // the number of terms limiting, active, from below found so far
        numeric_pair<mpq> bound_plus = numeric_pair<mpq>(0, 0); // the partial sum for plus, seen so far
        bool interested_in_plus = true;

        for (unsigned i : m_core_solver.m_pivot_row.m_index) {
            propogate_bound_on_var_on_coeff(i,
                                            m_core_solver.m_pivot_row[i]);
        }
        propogate_bound_on_var_on_coeff(m_solver.m_basis[m_row_index],
                                        one_of_type<mpq>());
        if (interested_in_minus)
            propogate_for_minus();
        if (interested_in_plus)
            propogate_for_plus();
}

void bound_propagator::propogate_bound_on_var_on_coeff(int j, const mpq &a) {
    int  sign = 0;
    switch (m_core_solver.m_column_type[j]) {
    case boxed:
    case fixed:
        propogate_bound_on_pivot_row_one_var_case_boxed_fixed(j, a); 
        break;
    case low_bound:
        sign = a.is_pos();
        break;
    case upper_bound:
        sign = !a.is_pos();
        break;
    case free_column:
        if (m_interested_in_minus) {
            if (m_cand_minus == -1)
                m_cand_minus = j; 
            else
                m_interested_in_minus = false; // it is the second growing term; cannot pin both
        }
        if (m_interested_in_plus) {
            if (m_cand_plus == -1)
                m_cand_plus = j; 
            else
                m_interested_in_plus = false; // it is the second diminishing term; cannot pin both
        }
    }
    if (sign) {
        propogate_bound_on_pivot_row_one_var_case_low_upper(a, sign, j);
    }
}
void bound_propagator::propogate_bound_on_pivot_row_one_var_case_boxed_fixed(int j, const mpq & a) {
    if (m_interested_in_minus) {
        m_bound_minus += a * (a.is_pos() ? m_solver.m_upper_bounds()[j] : m_solver.m_low_bounds()[j]); 
        m_n_minus++;
    }
    if (m_interested_in_plus) {
        m_bound_minus += a * (a.is_pos() ? m_solver.m_low_bounds()[j] : m_solver.m_upper_bounds()[j]); 
        m_n_plus++;
    }
}

void bound_propagator::propogate_for_plus() {
    if (m_n_plus < m_core_solver.m_pivot_row.m_index.size())
        return; // cannot pin anything
    if (m_n_plus == m_core_solver.m_pivot_row.m_index.size()) {
        lean_assert(m_cand_plus != -1);
        bound_evidence bnd_evid;
        bnd_evid.m_j = m_cand_plus;
        fill_bound_evidence_plus(bnd_evid);
        m_bound_evidences.push_back(bnd_evid);
    } else {
        lean_assert(m_n_plus == m_core_solver.m_pivot_row.m_index.size() + 1);
        std::cout << "can try to pin everybody" << std::endl;
        
    }
}
void bound_propagator::fill_bound_evidence_plus(bound_evidence & bnd_evid) {
    auto bound_val = zero_of_type<numeric_pair<mpq>>();
    for (unsigned i : m_core_solver.m_pivot_row.m_index)
        fill_bound_evidence_plus_on_coeff(i, m_core_solver.m_pivot_row.m_data[i], bnd_evid);
    fill_bound_evidence_plus_on_coeff(m_solver.m_basis[m_row_index], one_of_type<mpq>(), bnd_evid);   
}

void bound_propagator::fill_bound_evidence_plus_on_coeff(unsigned j, const mpq & a, bound_evidence & be) {
    std::cout << "fill_bound_evidence_plus_on_coeff\n";
    std::cout << "j = " << j << " a = " << a << "\n";
    std::cout << "j type is " << column_type_to_string(m_solver.m_column_types()[j]) << "\n";
    std::cout << "bound plus is " << m_bound_plus << "\n";
    // we have to have a * x[j] <= m_bound_plus
    // let us consider cases
    if (a.is_pos())
        fill_bound_evidence_plus_on_coeff_a_pos(j, a, be);
    else
        fill_bound_evidence_plus_on_coeff_a_neg(j, a, be);
}

void bound_propagator::fill_bound_evidence_plus_on_coeff_a_pos(unsigned j, const mpq & a, bound_evidence & be) {}
void bound_propagator::fill_bound_evidence_plus_on_coeff_a_neg(unsigned j, const mpq & a, bound_evidence & be) {}    
    
void bound_propagator::propogate_for_minus() {
    if (m_n_minus < m_core_solver.m_pivot_row.m_index.size())
        return; // cannot pin anything
    if (m_n_minus == m_core_solver.m_pivot_row.m_index.size()) {
        lean_assert(m_cand_minus != -1);
        std::cout << "good case min" << std::endl;
    } else {
        lean_assert(m_n_minus == m_core_solver.m_pivot_row.m_index.size() + 1);
        std::cout << "can try to pin everybody" << std::endl;
    }
}
    void bound_propagator::propogate_bound_on_pivot_row_one_var_case_low_upper(const mpq& a,
                                                             int sign, // sign > 0 means the term can grow, sign < 0 means term can decrease
                                                             int j) {
        if (sign > 0){
            if (m_interested_in_plus) {
                m_bound_plus += a * (a.is_pos() ? m_solver.m_low_bounds()[j] : m_solver.m_upper_bounds()[j]); 
                m_n_plus++;
            }
            if (m_interested_in_minus) {
                if (m_cand_minus == -1)
                    m_cand_minus = j;
                else
                    m_interested_in_minus = false; // it is the second growing term; cannot pin both
            }
        } else {
            if (m_interested_in_minus) {
                m_bound_minus += a * (a.is_pos() ? m_solver.m_upper_bounds()[j] : m_solver.m_low_bounds()[j]); 
                m_n_minus++;
            }
            if (m_interested_in_plus) {
                if (m_cand_plus == -1)
                    m_cand_plus = j;
                else
                    m_interested_in_plus = false; // it is the second diminishing term; cannot pin both
            }
        }
    }

}
