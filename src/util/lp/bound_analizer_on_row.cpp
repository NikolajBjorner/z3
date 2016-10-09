/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/bound_analizer_on_row.h"
#include "util/lp/lar_solver.h"
namespace lean {
template <typename T, typename X>    
void bound_analizer_on_row<T, X>::analyze() {
      // We have the equality sum by j of row[j]*x[j] = 0
    // We try to pin a var by pushing the total of the partial sum down, denoting the variable of this process by _minus.
    // In the same loop trying to pin a var by pushing the partial sum up, denoting it by _plus

    m_it.reset();
    T a;
    unsigned i;
    while (m_it.next(a, i) && (m_interested_in_minus || m_interested_in_plus)) {
        m_n_total++;
        analyze_bound_on_var_on_coeff(i, a);
    }

    if (m_interested_in_minus)
        analyze_for_minus();
    if (m_interested_in_plus)
        analyze_for_plus();
 }

template <typename T, typename X>    
void bound_analizer_on_row<T, X>::analyze_bound_on_var_on_coeff(int j, const T &a) {
    int  sign = 0;
    switch (m_column_types[j]) {
    case boxed:
    case fixed:
        analyze_bound_on_pivot_row_one_var_case_boxed_fixed(j, a); 
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
        analyze_bound_on_pivot_row_one_var_case_low_upper(a, sign, j);
    }
}
template <typename T, typename X>    
void bound_analizer_on_row<T, X>::analyze_bound_on_pivot_row_one_var_case_boxed_fixed(int j, const T & a) {
    if (m_interested_in_minus) {
        m_bound_minus += a * (a.is_pos() ? m_upper_bounds[j] : m_low_bounds[j]); 
        m_n_minus++;
    }
    if (m_interested_in_plus) {
        m_bound_plus += a * (a.is_pos() ? m_low_bounds[j] : m_upper_bounds[j]); 
        m_n_plus++;
    }
}

template <typename T, typename X>    
void bound_analizer_on_row<T, X>::pin_for_total_case_plus(const T & a, unsigned j) {
    implied_bound_evidence_signature<T, X> be;
    be.m_j = j;
    m_cand_plus = j;
    m_a_plus = a;
    auto bound_correction = a.is_pos() ? m_low_bounds[j]: m_upper_bounds[j];
    m_bound_plus -= bound_correction;
    fill_bound_evidence_plus(be);
    m_bound_plus+= bound_correction;
}
template <typename T, typename X>    
void bound_analizer_on_row<T, X>::pin_for_total_case_minus(const T & a, unsigned j) {
    implied_bound_evidence_signature<T, X> be;
    be.m_j = j;
    m_cand_minus = j;
    m_a_minus = a;
    auto bound_correction = (!a.is_pos()) ? m_low_bounds[j] : m_upper_bounds[j];
    m_bound_minus -= bound_correction;
    fill_bound_evidence_minus(be);
    m_bound_minus += bound_correction;
}

template <typename T, typename X>    
void bound_analizer_on_row<T, X>::analyze_for_plus() {
    if (m_n_plus < m_n_total - 1)
        return; // cannot pin anything
    if (m_n_plus == m_n_total - 1) {
        lean_assert(m_cand_plus != -1);
        implied_bound_evidence_signature<T, X> bnd_evid;
        bnd_evid.m_j = m_cand_plus;
        fill_bound_evidence_plus(bnd_evid);
    } else {
        lean_assert(m_n_plus == m_n_total);
        auto it = m_it.clone();
        T a;
        
        unsigned j;
        while (it->next(a, j))
            pin_for_total_case_plus(a, j);
    }
}

template <typename T, typename X>    
void bound_analizer_on_row<T, X>::fill_bound_evidence_minus(implied_bound_evidence_signature<T, X> & bnd_evid) {
    bool found = m_a_minus.is_pos()?  fill_bound_kind_minus_on_pos(bnd_evid) :
        fill_bound_kind_minus_on_neg(bnd_evid);
    if (!found)
        return;
    implied_bound_evidence_signature<T, X> & registered_be = m_evidence_vector[m_evidence_vector.size() - 1];
    auto it = m_it.clone();
    T a; unsigned i;
    while (it->next(a, i)) 
        fill_bound_evidence_sign_on_coeff(-1, i, a, registered_be);
    delete it;
    // m_solver.print_bound_evidence(registered_be);
}

template <typename T, typename X>    
void bound_analizer_on_row<T, X>::fill_bound_evidence_plus(implied_bound_evidence_signature<T, X> & bnd_evid) {
    bool found = m_a_plus.is_pos()? fill_bound_kind_plus_on_pos(bnd_evid)
        : fill_bound_kind_plus_on_neg(bnd_evid);
    if (!found )
        return;
    auto &registered_be = m_evidence_vector[m_evidence_vector.size() - 1];
    T a; unsigned i;
    auto it = m_it.clone();
    while (it->next(a, i)) 
        fill_bound_evidence_sign_on_coeff(1, i, a, registered_be);
    delete it;
}
    
template <typename T, typename X>    
bool bound_analizer_on_row<T, X>::fill_bound_kind_plus_on_pos(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(m_a_plus.is_pos());
    // we have sum a[k]x[k] + m_a_plus * x[m_cand_plus] = 0;
    // so a*x[m_cand_plus] = - a[k]x[k] <=  - m_bound_plus
    // we have to have a * x[m_cand_plus] <= - m_bound_plus, or x[m_cand_plus] <= -m_bound_plus / a, sin
    // so we have an upper bound
    auto u = -m_bound_plus / m_a_plus;
    switch (m_column_types[m_cand_plus]) {
    case boxed:
    case fixed:
    case upper_bound: // in all these cases we have an upper bound already
        if (u >= m_upper_bounds[m_cand_plus]) return false; 
        break;
    default:
        break;
    }
    // got a new upper bound
    be.m_low_bound = false;

    lean_assert(be.m_j == static_cast<unsigned>(m_cand_plus));
    be.m_bound = u;
    m_evidence_vector.push_back(be);
    return true;
}

template <typename T, typename X>    
bool bound_analizer_on_row<T, X>::fill_bound_kind_plus_on_neg(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(m_a_plus.is_neg());
    // we have sum a[k]x[k] + m_a_plus * x[m_cand_plus] = 0;
    // so m_a_plus *x[m_cand_plus] = - sum a[k]x[k] <=  - m_bound_plus
    // we have to have m_a_plus * x[m_cand_plus] <= - m_bound_plus, or x[m_cand_plus] >= -m_bound_plus / m_a_plus, since m_a_plus is negative
    // so we have a low bound
    auto l = -m_bound_plus / m_a_plus;
    switch (m_column_types[m_cand_plus]) {
    case low_bound:
    case fixed:
    case boxed:
        // in all these cases we have a low bound for x[m_cand_plus] already
        if (l <= m_low_bounds[m_cand_plus]) return false;
    default:
        break;
    }
    // got a new low bound
    be.m_low_bound = true;
    be.m_bound = l;
    //register the new bound
    m_evidence_vector.push_back(be);
    return true;
}
    
template <typename T, typename X>    
void bound_analizer_on_row<T, X>::fill_bound_evidence_sign_on_coeff(int sign, unsigned j, const T & a, implied_bound_evidence_signature<T, X> & be) {
    if (j == static_cast<unsigned>(be.m_j)) return;
    int a_sign = a.is_pos()? 1: -1;
    sign *= a_sign;
    bound_signature<T> bsig(a, j, sign > 0);
    be.m_evidence.emplace_back(bsig);
}

template <typename T, typename X>    
void bound_analizer_on_row<T, X>::analyze_for_minus() {
    if (m_n_minus < m_n_total - 1)
        return; // cannot pin anything
    if (m_n_minus == m_n_total - 1) {
        lean_assert(m_cand_minus != -1);
        implied_bound_evidence_signature<T, X> bnd_evid;
        bnd_evid.m_j = m_cand_minus;
        fill_bound_evidence_minus(bnd_evid);
    } else {
        lean_assert(m_n_minus == m_n_total);
        auto it = m_it.clone();
        T a;
        unsigned j;
        while (it->next(a, j)) {
            pin_for_total_case_minus(a, j);
        }
        delete it;
    }
}

template <typename T, typename X>    
void bound_analizer_on_row<T, X>::analyze_bound_on_pivot_row_one_var_case_low_upper(const T& a,
                                                                                    int sign, // sign > 0 means the term can grow, sign < 0 means term can decrease
                                                                                    int j) {
    if (sign > 0){
        if (m_interested_in_plus) {
            m_bound_plus += a * (a.is_pos() ? m_low_bounds[j] : m_upper_bounds[j]); 
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
            m_bound_minus += a * (a.is_pos() ? m_upper_bounds[j] : m_low_bounds[j]); 
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

template <typename T, typename X>    
bool bound_analizer_on_row<T, X>::fill_bound_kind_minus_on_pos(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(m_a_minus.is_pos());
    // we have sum a[k]x[k] + m_a_minus * x[m_cand_minus] = 0;
    // so a*x[m_cand_minus] = - sum a[k]x[k] >=  - m_bound_minus
    // we have to have a * x[m_cand_minus] >= - m_bound_minus, or x[m_cand_minus] >= -m_bound_minus / a, 
    // so we have a low bound
    auto l = -m_bound_minus / m_a_minus;
    switch (m_column_types[m_cand_minus]) {
    case boxed:
    case fixed:
    case low_bound: // in all these cases we have an upper bound already
        if (l >= m_low_bounds[m_cand_minus]) return false; 
        break;
    default:
        break;
    }
    // got a new low bound
    be.m_low_bound = true;
    lean_assert(be.m_j = m_cand_minus);
    be.m_bound = l;
    m_evidence_vector.push_back(be);
    return true;
}

template <typename T, typename X>    
bool bound_analizer_on_row<T, X>::fill_bound_kind_minus_on_neg(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(m_a_minus.is_neg());
    // we have sum a[k]x[k] + m_a_minus * x[m_cand_minus] = 0;
    // so m_a_minus *x[m_cand_minus] = - a[k]x[k] >=  - m_bound_minus
    // we have to have m_a_minus * x[m_cand_minus] >= - m_bound_minus, or x[m_cand_minus] <= -m_bound_minus / m_a_minus, since m_a_minus is negative
    // so we have an upper bound
    auto u = -m_bound_minus / m_a_minus;
    switch (m_column_types[m_cand_minus]) {
    case upper_bound:
    case fixed:
    case boxed:
        // in all these cases we have an upper bound for x[m_cand_minus] already
        if (u >= m_upper_bounds[m_cand_minus]) return false;
    default:
        break;
    }
    // got a new upper bound
    be.m_low_bound = false;
    be.m_bound = u;
    m_evidence_vector.push_back(be);
    return true;
}

template void bound_analizer_on_row<mpq, numeric_pair<mpq> >::analyze();

}
