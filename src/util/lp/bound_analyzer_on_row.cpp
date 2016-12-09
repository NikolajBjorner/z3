/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/bound_analyzer_on_row.h"
#include "util/lp/lar_solver.h"
namespace lean {
template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::analyze() {
      // We have the equality sum by j of row[j]*x[j] = m_rs
    // We try to pin a var by pushing the total of the partial sum down, denoting the variable of this process by _u.
    // In the same loop trying to pin a var by pushing the partial sum up, denoting it by _l

    m_it.reset();
    T a;
    unsigned i;
    while ((m_interested_in_u || m_interested_in_l) && m_it.next(a, i) ) {
        m_n_total++;
        analyze_bound_on_var_on_coeff(i, a);
    }

    if (m_interested_in_u)
        analyze_for_u();
    if (m_interested_in_l)
        analyze_for_l();
 }

template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::analyze_bound_on_var_on_coeff(int j, const T &a) {
    int  sign = 0;
    switch (m_column_types(j)) {
    case boxed:
    case fixed:
        analyze_bound_on_row_one_var_case_boxed_fixed(j, a); 
        break;
    case low_bound:
        sign = numeric_traits<T>::is_pos(a)? 1:-1;
        break;
    case upper_bound:
        sign = -(numeric_traits<T>::is_pos(a) ? 1 : -1);
        break;
    case free_column:
        if (m_interested_in_u) {
            if (m_cand_u == -1) {
                m_cand_u = j; 
                m_a_u = a;
            }
            else
                m_interested_in_u = false; // it is the second growing term; cannot pin both
        }
        if (m_interested_in_l) {
            if (m_cand_l == -1) {
                m_cand_l = j; 
                m_a_l = a;
            }
            else
                m_interested_in_l = false; // it is the second diminishing term; cannot pin both
        }
    }
    if (sign) {
        analyze_bound_on_row_one_var_case_low_upper(a, sign, j);
    }
}
template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::analyze_bound_on_row_one_var_case_boxed_fixed(int j, const T & a) {
    if (m_interested_in_u) {
        m_bound_u += a * (numeric_traits<T>::is_pos(a) ? m_upper_bounds[j] : m_low_bounds[j]); 
        m_n_u++;
    }
    if (m_interested_in_l) {
        m_bound_l += a * (numeric_traits<T>::is_pos(a) ? m_low_bounds[j] : m_upper_bounds[j]); 
        m_n_l++;
    }
}

template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::pin_for_total_case_l(const T & a, unsigned j) {
    implied_bound_evidence_signature<T, X> be;
    be.m_j = j;
    m_cand_l = j;
    m_a_l = a;
    auto bound_correction = a * (numeric_traits<T>::is_pos(a) ? m_low_bounds[j]: m_upper_bounds[j]);
    X saved_bound = m_bound_l;
    m_bound_l -= bound_correction;
    if (m_provide_evidence)
        fill_bound_evidence_l(be);
    m_bound_l = saved_bound;
}
template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::pin_for_total_case_u(const T & a, unsigned j) {
    implied_bound_evidence_signature<T, X> be;
    be.m_j = j;
    m_cand_u = j;
    m_a_u = a;
    auto bound_correction = a * (numeric_traits<T>::is_pos(a) ? m_upper_bounds[j] : m_low_bounds[j]);
    X saved_bound = m_bound_u; 
    m_bound_u -= bound_correction;
    fill_bound_evidence_u(be);
    m_bound_u = saved_bound;
}

template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::analyze_for_l() {
    if (m_n_l < m_n_total - 1)
        return; // cannot pin anything
    if (m_n_l == m_n_total - 1) {
        lean_assert(m_cand_l != -1);
        implied_bound_evidence_signature<T, X> bnd_evid;
        bnd_evid.m_j = m_cand_l;
        fill_bound_evidence_l(bnd_evid);
    } else {
        lean_assert(m_n_l == m_n_total);
        auto it = m_it.clone();
        T a;
        
        unsigned j;
        while (it->next(a, j))
            pin_for_total_case_l(a, j);
    }
}

template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::fill_bound_evidence_u(implied_bound_evidence_signature<T, X> & bnd_evid) {
    bool found = numeric_traits<T>::is_pos(m_a_u)?  fill_bound_kind_u_on_pos(bnd_evid) :
        fill_bound_kind_u_on_neg(bnd_evid);
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
void bound_analyzer_on_row<T, X>::fill_bound_evidence_l(implied_bound_evidence_signature<T, X> & bnd_evid) {
    bool found = numeric_traits<T>::is_pos(m_a_l)? fill_bound_kind_plus_on_pos(bnd_evid)
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
bool bound_analyzer_on_row<T, X>::fill_bound_kind_plus_on_pos(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(numeric_traits<T>::is_pos(m_a_l));
    // we have sum a[k]x[k] + m_a_l * x[m_cand_l] = m_rs;
    // so a*x[m_cand_l] = m_rs - a[k]x[k] <=  - m_bound_l
    // we have to have a * x[m_cand_l] <= - m_bound_l, or x[m_cand_l] <= -m_bound_l / a, sin
    // so we have an upper bound
    auto u = - m_bound_l / m_a_l;
    switch (m_column_types(m_cand_l)) {
    case boxed:
    case fixed:
    case upper_bound: // in all these cases we have an upper bound already
        if (u >= m_upper_bounds[m_cand_l]) return false; 
        break;
    default:
        break;
    }
    // got a new upper bound
    be.m_low_bound = false;
    lean_assert(be.m_j == static_cast<unsigned>(m_cand_l));
    be.m_bound = u;
    m_evidence_vector.push_back(be);
    return true;
}

template <typename T, typename X>    
bool bound_analyzer_on_row<T, X>::fill_bound_kind_plus_on_neg(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(numeric_traits<T>::is_neg(m_a_l));
    // we have sum a[k]x[k] + m_a_l * x[m_cand_l] = m_rs;
    // so m_a_l *x[m_cand_l] = m_rs - sum a[k]x[k] <= m_rs - m_bound_l
    // we have to have m_a_l * x[m_cand_l] <= m_rs - m_bound_l, or x[m_cand_l] >= (m_rs -m_bound_l) / m_a_l, since m_a_l is negative
    // so we have a low bound
    auto l = - m_bound_l / m_a_l;
    switch (m_column_types(m_cand_l)) {
    case low_bound:
    case fixed:
    case boxed:
        // in all these cases we have a low bound for x[m_cand_l] already
        if (l <= m_low_bounds[m_cand_l]) return false;
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
void bound_analyzer_on_row<T, X>::fill_bound_evidence_sign_on_coeff(int sign, unsigned j, const T & a, implied_bound_evidence_signature<T, X> & be) {
    if (j == static_cast<unsigned>(be.m_j)) return;
    int a_sign = numeric_traits<T>::is_pos(a)? 1: -1;
    sign *= a_sign;
    bound_signature<T> bsig(a, j, sign > 0);
    be.m_evidence.emplace_back(bsig);
}

template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::analyze_for_u() {
    if (m_n_u < m_n_total - 1)
        return; // cannot pin anything
    if (m_n_u == m_n_total - 1) {
        lean_assert(m_cand_u != -1);
        implied_bound_evidence_signature<T, X> bnd_evid;
        bnd_evid.m_j = m_cand_u;
        if (m_provide_evidence)
            fill_bound_evidence_u(bnd_evid);
    } else {
        lean_assert(m_n_u == m_n_total);
        auto it = m_it.clone();
        T a;
        unsigned j;
        while (it->next(a, j)) {
            pin_for_total_case_u(a, j);
        }
        delete it;
    }
}

template <typename T, typename X>    
void bound_analyzer_on_row<T, X>::analyze_bound_on_row_one_var_case_low_upper(const T& a,
                                                                                    int sign, // sign > 0 means the term can grow, sign < 0 means term can decrease
                                                                                    int j) {
    if (sign > 0){
        if (m_interested_in_l) {
            m_bound_l += a * (numeric_traits<T>::is_pos(a) ? m_low_bounds[j] : m_upper_bounds[j]); 
            m_n_l++;
        }
        if (m_interested_in_u) {
            if (m_cand_u == -1){
                m_cand_u = j;
                m_a_u = a;
            }
            else
                m_interested_in_u = false; // it is the second growing term; cannot pin both
        }
    } else {
        if (m_interested_in_u) {
            m_bound_u += a * (numeric_traits<T>::is_pos(a) ? m_upper_bounds[j] : m_low_bounds[j]); 
            m_n_u++;
        }
        if (m_interested_in_l) {
            if (m_cand_l == -1) {
                m_cand_l = j;
                m_a_l = a;
            }
            else
                m_interested_in_l = false; // it is the second diminishing term; cannot pin both
        }
    }
}

template <typename T, typename X>    
bool bound_analyzer_on_row<T, X>::fill_bound_kind_u_on_pos(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(numeric_traits<T>::is_pos(m_a_u));
    // we have sum a[k]x[k] + m_a_u * x[m_cand_u] = m_rs;
    // so a*x[m_cand_u] = m_rs - sum a[k]x[k] >= m_rs - m_bound_u
    // we have to have a * x[m_cand_u] >= m_rs - m_bound_u, or x[m_cand_u] >= (m_rs-m_bound_u) / a, 
    // so we have a low bound
    auto l =  - m_bound_u / m_a_u;
    switch (m_column_types(m_cand_u)) {
    case boxed:
    case fixed:
    case low_bound: // in all these cases we have a low bound already
        if (l <= m_low_bounds[m_cand_u]) return false; 
        break;
    default:
        break;
    }
    // got a new low bound
    be.m_low_bound = true;
    lean_assert(be.m_j == m_cand_u);
    be.m_bound = l;
    m_evidence_vector.push_back(be);
    return true;
}

template <typename T, typename X>    
bool bound_analyzer_on_row<T, X>::fill_bound_kind_u_on_neg(implied_bound_evidence_signature<T, X>& be) {
    lean_assert(numeric_traits<T>::is_neg(m_a_u));
    // we have sum a[k]x[k] + m_a_u * x[m_cand_u] = m_rs;
    // so m_a_u *x[m_cand_u] = m_rs - a[k]x[k] >= m_rs - m_bound_u
    // we have to have m_a_u * x[m_cand_u] >= m_rs- m_bound_u, or x[m_cand_u] <= (m_rs - m_bound_u) / m_a_u, since m_a_u is negative
    // so we have an upper bound
    auto u = - m_bound_u / m_a_u;
    switch (m_column_types(m_cand_u)) {
    case upper_bound:
    case fixed:
    case boxed:
        // in all these cases we have an upper bound for x[m_cand_u] already
        if (u >= m_upper_bounds[m_cand_u]) return false;
    default:
        break;
    }
    // got a new upper bound
    be.m_low_bound = false;
    lean_assert(be.m_j == m_cand_u);
    be.m_bound = u;
    m_evidence_vector.push_back(be);
    return true;
}

template void bound_analyzer_on_row<mpq, numeric_pair<mpq> >::analyze();
template void bound_analyzer_on_row<mpq, mpq>::analyze(void);
template void bound_analyzer_on_row<double, double>::analyze(void);
}
