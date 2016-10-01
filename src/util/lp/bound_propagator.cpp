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
        std::cout << "pivot row\n";
        m_core_solver.m_pivot_row.print(std::cout);
                // We have the equality, sum by j of pivot_row[j]*x[j] + x[basis[j]] = 0
        // We try to pin a var by pushing the total of the partial sum down, denoting the variable of this process by _minus.
        // In the same loop trying to pin a var by pushing the partial sum up, denoting it by _plus
        
        for (unsigned i : m_core_solver.m_pivot_row.m_index) {
            propagate_bound_on_var_on_coeff(i,
                                            m_core_solver.m_pivot_row[i]);
        }
        propagate_bound_on_var_on_coeff(m_solver.m_basis[m_row_index],
                                        one_of_type<mpq>());
        if (m_interested_in_minus)
            propagate_for_minus();
        if (m_interested_in_plus)
            propagate_for_plus();
}

void bound_propagator::propagate_bound_on_var_on_coeff(int j, const mpq &a) {
    int  sign = 0;
    switch (m_core_solver.m_column_type[j]) {
    case boxed:
    case fixed:
        propagate_bound_on_pivot_row_one_var_case_boxed_fixed(j, a); 
        break;
    case low_bound:
        sign = a.is_pos()? 1:-1;
        break;
    case upper_bound:
        sign = -(a.is_pos() ? 1 : -1);
        break;
    case free_column:
        if (m_interested_in_minus) {
            if (m_cand_minus == -1) {
                m_cand_minus = j; 
                m_a_minus = a;
            }
            else
                m_interested_in_minus = false; // it is the second growing term; cannot pin both
        }
        if (m_interested_in_plus) {
            if (m_cand_plus == -1) {
                m_cand_plus = j; 
                m_a_plus = a;
            }
            else
                m_interested_in_plus = false; // it is the second diminishing term; cannot pin both
        }
    }
    if (sign) {
        propagate_bound_on_pivot_row_one_var_case_low_upper(a, sign, j);
    }
}
void bound_propagator::propagate_bound_on_pivot_row_one_var_case_boxed_fixed(int j, const mpq & a) {
    if (m_interested_in_minus) {
        m_bound_minus += a * (a.is_pos() ? m_solver.m_upper_bounds()[j] : m_solver.m_low_bounds()[j]); 
        m_n_minus++;
    }
    if (m_interested_in_plus) {
        m_bound_plus += a * (a.is_pos() ? m_solver.m_low_bounds()[j] : m_solver.m_upper_bounds()[j]); 
        m_n_plus++;
    }
}

void bound_propagator::propagate_for_plus() {
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
void bound_propagator::fill_bound_evidence_minus(bound_evidence & bnd_evid) {
    if (m_a_plus.is_pos() )
        fill_bound_kind_minus_on_pos(bnd_evid);
    else
        fill_bound_kind_minus_on_neg(bnd_evid);
    for (unsigned i : m_core_solver.m_pivot_row.m_index)
        fill_bound_evidence_sign_on_coeff(-1, i, m_core_solver.m_pivot_row.m_data[i], bnd_evid);
    fill_bound_evidence_sign_on_coeff(-1, m_solver.m_basis[m_row_index], one_of_type<mpq>(), bnd_evid);   
}

void bound_propagator::fill_bound_evidence_plus(bound_evidence & bnd_evid) {
    if (m_a_plus.is_pos() )
        fill_bound_kind_plus_on_pos(bnd_evid);
    else
        fill_bound_kind_plus_on_neg(bnd_evid);
    for (unsigned i : m_core_solver.m_pivot_row.m_index)
        fill_bound_evidence_sign_on_coeff(1, i, m_core_solver.m_pivot_row.m_data[i], bnd_evid);
    fill_bound_evidence_sign_on_coeff(1, m_solver.m_basis[m_row_index], one_of_type<mpq>(), bnd_evid);   
}


    
void bound_propagator::fill_bound_kind_plus_on_pos(bound_evidence& be) {
    lean_assert(m_a_plus.is_pos());
    // we have sum a[k]x[k] + m_a_plus * x[m_cand_plus] = 0;
    // so a*x[m_cand_plus] = - a[k]x[k] <=  - m_bound_plus
    // we have to have a * x[m_cand_plus] <= - m_bound_plus, or x[m_cand_plus] <= -m_bound_plus / a, sin
    // so we have a low bound
    auto l = -m_bound_plus / m_a_plus;
    switch (m_core_solver.m_column_type[m_cand_plus]) {
    case boxed:
    case fixed:
    case low_bound: // in all these cases we have an upper bound already
        if (l <= m_core_solver.m_low_bounds[m_cand_plus]) return; 
        break;
    default:
        break;
    }

    lean_assert(be.m_j = m_cand_plus);
    // got a new upper bound
    if (is_zero(l.y)) {
        be.m_kind = LE;
    } else {
        be.m_kind = LT; // strict case
    }
    be.m_bound = l.x;
}
void bound_propagator::fill_bound_kind_plus_on_neg(bound_evidence& be) {
    lean_assert(m_a_plus.is_neg());
    // we have sum a[k]x[k] + m_a_plus * x[m_cand_plus] = 0;
    // so m_a_plus *x[m_cand_plus] = - sum a[k]x[k] <=  - m_bound_plus
    // we have to have m_a_plus * x[m_cand_plus] <= - m_bound_plus, or x[m_cand_plus] >= -m_bound_plus / m_a_plus, since m_a_plus is negative
    // so we have an upper bound
    auto l = -m_bound_plus / m_a_plus;
    switch (m_core_solver.m_column_type[m_cand_plus]) {
    case low_bound:
    case fixed:
    case boxed:
        // in all these cases we have an upper bound for x[m_cand_plus] already
        if (l <= m_core_solver.m_low_bounds[m_cand_plus]) return;
    default:
        break;
    } // got a new upper bound
    if (is_zero(l.y)) {
        be.m_kind = GE;
    }
    else {
        be.m_kind = GT; // strict case
    }
    be.m_bound = l.x;
}
    
void bound_propagator::fill_bound_evidence_sign_on_coeff(int sign, unsigned j, const mpq & a, bound_evidence & be) {
    if (j == m_cand_plus) return;
    int a_sign = a.is_pos()? 1: -1;
    sign *= a_sign;
    const canonic_left_side & cls = m_solver.m_vec_of_canonic_left_sides[j];
    const ul_pair & ul = m_solver.m_map_of_canonic_left_sides_to_ul_pairs[cls];
    constraint_index witness = sign > 0? ul.m_low_bound_witness: ul.m_upper_bound_witness;
    be.m_evidence.emplace_back(a, witness);

}

void bound_propagator::propagate_for_minus() {
    if (m_n_minus < m_core_solver.m_pivot_row.m_index.size())
        return; // cannot pin anything
    if (m_n_minus == m_core_solver.m_pivot_row.m_index.size()) {
        lean_assert(m_cand_minus != -1);
        bound_evidence bnd_evid;
        bnd_evid.m_j = m_cand_minus;
        fill_bound_evidence_minus(bnd_evid);
        m_bound_evidences.push_back(bnd_evid);
    } else {
        lean_assert(m_n_minus == m_core_solver.m_pivot_row.m_index.size() + 1);
        std::cout << "can try to pin everybody" << std::endl;
    }
}

void bound_propagator::propagate_bound_on_pivot_row_one_var_case_low_upper(const mpq& a,
                                                             int sign, // sign > 0 means the term can grow, sign < 0 means term can decrease
                                                             int j) {
        if (sign > 0){
            if (m_interested_in_plus) {
                m_bound_plus += a * (a.is_pos() ? m_solver.m_low_bounds()[j] : m_solver.m_upper_bounds()[j]); 
                m_n_plus++;
            }
            if (m_interested_in_minus) {
                if (m_cand_minus == -1){
                    m_cand_minus = j;
                    m_a_minus = a;
                }
                else
                    m_interested_in_minus = false; // it is the second growing term; cannot pin both
            }
        } else {
            if (m_interested_in_minus) {
                m_bound_minus += a * (a.is_pos() ? m_solver.m_upper_bounds()[j] : m_solver.m_low_bounds()[j]); 
                m_n_minus++;
            }
            if (m_interested_in_plus) {
                if (m_cand_plus == -1) {
                    m_cand_plus = j;
                    m_a_plus = a;
                }
                else
                    m_interested_in_plus = false; // it is the second diminishing term; cannot pin both
            }
        }
    }
void bound_propagator::fill_bound_kind_minus_on_pos(bound_evidence& be) {
    lean_assert(m_a_minus.is_pos());
    // we have sum a[k]x[k] + m_a_minus * x[m_cand_minus] = 0;
    // so a*x[m_cand_minus] = - sum a[k]x[k] >=  - m_bound_minus
    // we have to have a * x[m_cand_minus] >= - m_bound_minus, or x[m_cand_minus] >= -m_bound_minus / a, 
    // so we have a low bound
    auto l = -m_bound_minus / m_a_minus;
    switch (m_core_solver.m_column_type[m_cand_minus]) {
    case boxed:
    case fixed:
    case upper_bound: // in all these cases we have an upper bound already
        if (l >= m_core_solver.m_upper_bounds[m_cand_minus]) return; 
        break;
    default:
        break;
    }

    lean_assert(be.m_j = m_cand_minus);
    // got a new upper bound
    if (is_zero(l.y)) {
        be.m_kind = GE;
    } else {
        be.m_kind = GT; // strict case
    }
    be.m_bound = l.x;
}
void bound_propagator::fill_bound_kind_minus_on_neg(bound_evidence& be) {
    lean_assert(m_a_minus.is_neg());
    // we have sum a[k]x[k] + m_a_minus * x[m_cand_minus] = 0;
    // so m_a_minus *x[m_cand_minus] = - a[k]x[k] >=  - m_bound_minus
    // we have to have m_a_minus * x[m_cand_minus] >= - m_bound_minus, or x[m_cand_minus] <= -m_bound_minus / m_a_minus, since m_a_minus is negative
    // so we have a lower bound
    auto u = -m_bound_minus / m_a_minus;
    switch (m_core_solver.m_column_type[m_cand_minus]) {
    case low_bound:
    case fixed:
    case boxed:
        // in all these cases we have an upper bound for x[m_cand_minus] already
        if (u <= m_core_solver.m_low_bounds[m_cand_minus]) return;
    default:
        break;
    } // got a new upper bound
    if (is_zero(u.y)) {
        be.m_kind = LE;
    }
    else {
        be.m_kind = LT; // strict case
    }
    be.m_bound = u.x;
}

}
