/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include "util/lp/linear_combination_iterator.h"
#include "implied_bound_evidence_signature.h"
// We have an equality : sum by j of row[j]*x[j] = rs
// We try to pin a var by pushing the total by using the variable bounds
// In a loop we drive the partial sum down, denoting the variable of this process by _minus.
// In the same loop trying to pin variables by pushing the partial sum up, denoting it by _plus
namespace lean {
template <typename T, typename X> 
class bound_analyzer_on_row {
    
    linear_combination_iterator<T> & m_it;
    const std::vector<X>& m_low_bounds;
    const std::vector<X>& m_upper_bounds;
    const std::vector<column_type>& m_column_types;
    std::vector<implied_bound_evidence_signature<T, X>> & m_evidence_vector;
    
    int m_cand_minus = -1;  // the variable pinned from above
    T m_a_minus; // the coefficent before the minus candidate
    unsigned m_n_minus = 0; // the number of terms active, limiting from above found so far
    X m_bound_minus;
    bool m_interested_in_minus = true; // the partial sum for min, seen so far
    int m_cand_plus = -1;
    T m_a_plus; // the coefficent before the plus candidate
    unsigned m_n_plus = 0; // the number of terms limiting, active, from below found so far
    X m_bound_plus; // the partial sum for plus, seen so far
    bool m_interested_in_plus = true;
    unsigned m_n_total = 0;
    bool m_provide_evidence;
public :
    // constructor
    bound_analyzer_on_row(linear_combination_iterator<T> &it,
                          const std::vector<X>& low_bounds,
                          const std::vector<X>& upper_bounds,
                          const X& rs,
                          const std::vector<column_type>& column_types,
                          std::vector<implied_bound_evidence_signature<T, X>> & evidence_vector,
                          bool provide_evidence) :
        m_it(it),
        m_low_bounds(low_bounds),
        m_upper_bounds(upper_bounds),
        m_column_types(column_types),
        m_evidence_vector(evidence_vector),
        m_bound_minus(-rs),
        m_bound_plus(-rs),
        m_provide_evidence(provide_evidence)
    {}

    void analyze();
    void analyze_bound_on_var_on_coeff(int j, const T &a);
    void analyze_for_minus();
    void analyze_for_plus();
    void analyze_bound_on_row_one_var_case_boxed_fixed(int j, const T & a);
    void analyze_bound_on_row_one_var_case_low_upper(const T& a,
                                                             int sign, // sign > 0 means the term can grow, sign < 0 means term can decrease
                                                             int j);

    void fill_bound_evidence_plus(implied_bound_evidence_signature<T, X> & bnd_evid);
    void fill_bound_evidence_minus(implied_bound_evidence_signature<T, X> & bnd_evid);
    void fill_bound_evidence_sign_on_coeff(int sign, unsigned j, const T & a, implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_plus_on_pos(implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_plus_on_neg(implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_minus_on_pos(implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_minus_on_neg(implied_bound_evidence_signature<T, X> & be);
    void pin_for_total_case_plus(const T & a, unsigned j);
    void pin_for_total_case_minus(const T & a, unsigned j);
    static void analyze_row(linear_combination_iterator<T> &it,
                          const std::vector<X>& low_bounds,
                          const std::vector<X>& upper_bounds,
                          const X& rs,
                          const std::vector<column_type>& column_types,
                            std::vector<implied_bound_evidence_signature<T, X>> & evidence_vector,
                            bool provide_evidence) {
        bound_analyzer_on_row a(it, low_bounds, upper_bounds, rs, column_types, evidence_vector, provide_evidence);
        a.analyze();
    }

};
}
