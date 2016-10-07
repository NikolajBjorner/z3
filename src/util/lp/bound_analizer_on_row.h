/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/linear_combination_iterator.h"
#include "util/lp/implied_bound_evidence_signature.h"
namespace lean {
// We have an equality: sum it * x[j] = rs
template <typename T, typename X>
class bound_analizer_on_row {
    linear_combination_iterator<T>& m_it;
    const std::vector<X> & m_low_bounds;
    const std::vector<X> & m_upper_bounds;
    const std::vector<column_type> & m_column_types;
    const X & m_rs; // the right side
    std::vector<implied_bound_evidence_signature<X>>& m_implied_bound_signatures;
    
    // We have equality - sum by it**x[j] = rs

    int m_cand = -1;  // the variable pinned from above
    T m_a; // the coefficent before the candidate
    unsigned m_n = 0; // the number of active terms pushing towards m_dir
    X m_bound = X(0, 0);
    bool m_interested = true;
    int m_dir; // +1 when trying to pin by growing the expression, -1 by diminishing
    unsigned m_row_length = 0; // the total number of elems, this will be known only when we process all elements and don't exit prematurely
    // We pretend that we only try to induce new bounds by growing , so if m_dir is 1
    // the active terms are a * low_bound if a > 0, and a * upper_bound if a < 0.
    // m_dir = -1 reverses the search
    
public:
    bound_analizer_on_row(linear_combination_iterator<T> & it,
                          const std::vector<X> & low_bounds,
                          const std::vector<X> & upper_bounds,
                          const std::vector<column_type> & column_type,
                          const X &rs,
                          int direction,   
                          std::vector<implied_bound_evidence_signature<X>> &signatures  ) :
        m_it(it),
        m_low_bounds(low_bounds),
        m_upper_bounds(upper_bounds),
        m_column_types(column_type),
        m_rs(rs),
        m_implied_bound_signatures(signatures),
        m_dir(direction)
    {}

    const X& low_bound_val(unsigned j) const {
        return m_dir == 1? m_low_bounds[j] : m_upper_bounds[j];
    }

    const X& upper_bound_val(unsigned j) const {
        return m_dir == -1? m_low_bounds[j] : m_upper_bounds[j];
    }

    
    void analyze_on_elem_boxed_fixed(const T & a, unsigned j) {
        lean_assert(m_interested); 
        m_bound += a * (is_pos(a) ? low_bound_val(j) : upper_bound_val(j)); 
        m_n++;
    }

    void analyze_on_elem_low_upper(const T & a, int sign, unsigned j) {
        lean_assert(m_interested);
        // sign > 0 means the term can provide a low bound, sign < 0 means term can decrease
        if (sign < 0){
            if (m_cand == -1){
                m_cand = j;
                m_a = a;
            } else
                m_interested = false; // it is the second growing term; cannot pin both
        } else {
            m_bound += a * (is_pos(a) ? upper_bound_val(j) : low_bound_val(j)); 
            m_n++;
        }
    }


    column_type corrected_column_type(unsigned j) const {
        switch (m_column_types[j]) {
        case boxed:
        case fixed:
        case free_column:
            return m_column_types[j];
        case low_bound:
            return m_dir== 1? low_bound : upper_bound;
        case upper_bound:
            return m_dir== 1? upper_bound : low_bound;
        default:
            lean_assert(false);
        }
        lean_assert(false); // cannot be here
        throw "cannot be here";
    }

    template <typename L>
    bool is_pos(const L & a) const {
        return m_dir== 1? a.is_pos(): a.is_neg();
    }

    template <typename L>
    bool is_neg(const L & a) const {
        return m_dir== 1? a.is_neg(): a.is_pos();
    }

    
    void analyze_on_elem(const T & a, unsigned j) {
        m_row_length++;
        switch (m_column_types[j]) {
        case boxed:
        case fixed:
            analyze_on_elem_boxed_fixed(a, j); 
            break;
        case low_bound:
            analyze_on_elem_low_upper(a, is_pos(a)? 1:-1, j);
            break;
        case upper_bound:
            analyze_on_elem_low_upper(a, is_pos(a)? -1:1, j);
            break;
        case free_column:
            if (m_cand == -1) {
                m_cand = j; 
                m_a = a;
            } else {
                m_interested = false; // it is the second growing term; cannot pin both
            }
        }
    }

    void  total_case(const T & a, unsigned j) {
        implied_bound_evidence_signature<X> be;
        be.m_j = m_cand = j;
        m_a = a;
        auto bound_correction = a * (is_pos(a) ? low_bound_val(j): upper_bound_val(j));
        m_bound -= bound_correction;
        fill_bound_evidence(be);
        m_bound += bound_correction;
    }

    void fill_bound_evidence_on_pos(implied_bound_evidence_signature<X> & be) {
    // we have sum a[k]x[k] + m_a * x[m_cand] = 0;
    // so a*x[m_cand_plus] = - a[k]x[k] <=  - m_bound_plus
    // we have to have a * x[m_cand_plus] <= - m_bound_plus, or x[m_cand_plus] <= -m_bound_plus / a, sin
    // so we might have a new upper bound (module m_dir)
        auto u = - m_bound / m_a;
        switch(corrected_column_type(be.m_j)) {
        case fixed:
        case boxed:
        case upper_bound:
            if (!is_neg(u - upper_bound_val(be.m_j)))
                return; // we are not improving the existing bound
        default:
            break;
        }
        
        be.m_bound = u;
        be.m_low_bound = !(m_dir == 1);
        auto it = m_it.clone();

        T a;
        unsigned i;
        while (it->next(a, i)) {
            if (i == be.m_j)
                continue;
            bool at_low = is_pos(a);
            if (m_dir == -1)
                at_low = !at_low;
            bound_signature bound_sg(i, at_low);
            be.m_evidence.push_back(bound_sg);
        }
        delete it;
    }

    void fill_bound_evidence_on_neg(implied_bound_evidence_signature<X> & be) {
     // we have sum a[k]x[k] + m_a * x[m_cand] = 0;
    // so a*x[m_cand_plus] = - a[k]x[k] <=  - m_bound
    // we have to have a * x[m_cand_plus] <= - m_bound_plus, or x[m_cand_plus] >= -m_bound_plus / a, sinnce a is negative
    // so we might have a new lower bound (module m_dir)
        auto u = - m_bound / m_a;
        switch(corrected_column_type(be.m_j)) {
        case fixed:
        case boxed:
        case low_bound:
            if (!is_pos(u - upper_bound_val(be.m_j)))
                return; // we are not improving the existing bound
        default:
            break;
        }
        
        be.m_bound = u;
        be.m_low_bound = (m_dir == 1);
        auto it = m_it.clone();

        T a;
        unsigned i;
        while (it->next(a, i)) {
            if (i == be.m_j)
                continue;
            bool at_low = is_neg(a);
            if (m_dir == -1)
                at_low = !at_low;
            bound_signature bound_sg(i, at_low);
            be.m_evidence.push_back(bound_sg);
        }
        delete it;
    }
    
    void fill_bound_evidence(implied_bound_evidence_signature<X> & be) {
        if (is_pos(m_a) )
            fill_bound_evidence_on_pos(be);
        else
            fill_bound_evidence_on_neg(be);
    }
    
    void analyze_if_interested() {
        if (m_n < m_row_length - 1)
            return; // cannot pin anything
        if (m_n == m_row_length -1) {
            lean_assert(m_cand != -1);
            implied_bound_evidence_signature<X> bnd_evid;
            bnd_evid.m_j = m_cand;
            fill_bound_evidence(bnd_evid);
            this->m_implied_bound_signatures.push_back(bnd_evid);
        } else {
            lean_assert(m_n == m_row_length);
            auto local_it = m_it.clone();
            T a;
            unsigned j;
            while (local_it->next(a, j)) 
                total_case(a, j);
            delete local_it;
        }
    }

    void analyze() {
        T a;
        unsigned j;
        m_it.reset();
        while (m_it.next(a, j) && m_interested)
            analyze_on_elem(a, j);
        if (m_interested)
            analyze_if_interested();
    }
};
}
