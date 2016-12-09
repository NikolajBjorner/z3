/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include "util/lp/linear_combination_iterator.h"
#include "implied_bound_evidence_signature.h"
#include <functional>
// We have an equality : sum by j of row[j]*x[j] = rs
// We try to pin a var by pushing the total by using the variable bounds
// In a loop we drive the partial sum down, denoting the variables of this process by _u.
// In the same loop trying to pin variables by pushing the partial sum up, denoting the variable related to it by _l
namespace lean {
template <typename T, typename X> 
class bound_analyzer_on_row {
    
    linear_combination_iterator<T> & m_it;
    const std::vector<X>& m_low_bounds;
    const std::vector<X>& m_upper_bounds;
    std::function<column_type (unsigned)> m_column_types;
    std::vector<implied_bound_evidence_signature<T, X>> & m_evidence_vector;
    
    int m_cand_u = -1;  // the variable for which we found an uppper bound
    T m_a_u; // the coefficent before m_cand_u in the row
    unsigned m_n_u = 0; // the number of terms active, limiting from above found seen so far
    X m_bound_u; // the total upper bound
    bool m_interested_in_u = true; // the partial sum for min, seen so far
    int m_cand_l = -1;
    T m_a_l; // the coefficent before the plus candidate
    unsigned m_n_l = 0; // the number of terms limiting, active, from below found so seen far
    X m_bound_l; // the partial sum for plus, seen so far
    bool m_interested_in_l = true;
    unsigned m_n_total = 0;
    bool m_provide_evidence;
public :
    // constructor
    bound_analyzer_on_row(linear_combination_iterator<T> &it,
                          const std::vector<X> & low_bounds,
                          const std::vector<X> & upper_bounds,
                          const X& rs,
                          std::function<column_type (unsigned)> column_types,
                          std::vector<implied_bound_evidence_signature<T, X>> & evidence_vector,
                          bool provide_evidence) :
        m_it(it),
        m_low_bounds(low_bounds),
        m_upper_bounds(upper_bounds),
        m_column_types(column_types),
        m_evidence_vector(evidence_vector),
        m_bound_u(-rs),
        m_bound_l(-rs),
        m_provide_evidence(provide_evidence)
    {}

    void analyze();
    void analyze_bound_on_var_on_coeff(int j, const T &a);
    void analyze_for_u();
    void analyze_for_l();
    void analyze_bound_on_row_one_var_case_boxed_fixed(int j, const T & a);
    void analyze_bound_on_row_one_var_case_low_upper(const T& a,
                                                             int sign, // sign > 0 means the term can grow, sign < 0 means term can decrease
                                                             int j);

    void fill_bound_evidence_l(implied_bound_evidence_signature<T, X> & bnd_evid);
    void fill_bound_evidence_u(implied_bound_evidence_signature<T, X> & bnd_evid);
    void fill_bound_evidence_sign_on_coeff(int sign, unsigned j, const T & a, implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_plus_on_pos(implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_plus_on_neg(implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_u_on_pos(implied_bound_evidence_signature<T, X> & be);
    bool fill_bound_kind_u_on_neg(implied_bound_evidence_signature<T, X> & be);
    void pin_for_total_case_l(const T & a, unsigned j);
    void pin_for_total_case_u(const T & a, unsigned j);
    static void analyze_row(linear_combination_iterator<T> &it,
                            const std::vector<X>& low_bounds,
                            const std::vector<X>& upper_bounds,
                            const X& rs,
                            std::function<column_type (unsigned)> column_types,
                            std::vector<implied_bound_evidence_signature<T, X>> & evidence_vector,
                            bool provide_evidence) {
        bound_analyzer_on_row a(it, low_bounds, upper_bounds, rs, column_types, evidence_vector, provide_evidence);
        a.analyze();
    }

};
}
