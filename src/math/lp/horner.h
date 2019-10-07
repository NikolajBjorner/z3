/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once

#include "math/lp/nla_common.h"
#include "math/lp/nla_intervals.h"
#include "math/lp/nex.h"
#include "math/lp/cross_nested.h"
#include "math/lp/int_set.h"

namespace nla {
class core;


class horner : common {
    intervals             m_intervals;
    nex_sum               m_row_sum;
public:
    typedef intervals::interval interv;
    horner(core *core);
    void horner_lemmas();
    template <typename T> // T has an iterator of (coeff(), var())
    bool lemmas_on_row(const T&);
    template <typename T>  bool row_is_interesting(const T&) const;
    intervals::interval interval_of_expr_with_deps(const nex* e);
    intervals::interval interval_of_expr(const nex* e);
    intervals::interval interval_of_sum(const nex_sum*);
    intervals::interval interval_of_sum_no_term(const nex_sum*);
    intervals::interval interval_of_mul(const nex_mul*);
    void set_interval_for_scalar(intervals::interval&, const rational&);
    void set_var_interval(lpvar j, intervals::interval&) const;
    bool interval_from_term(const nex* e, interv&) const;

    
    intervals::interval interval_of_sum_with_deps(const nex_sum*);
    intervals::interval interval_of_sum_no_term_with_deps(const nex_sum*);
    intervals::interval interval_of_mul_with_deps(const nex_mul*);
    void set_var_interval_with_deps(lpvar j, intervals::interval&) const;
    bool lemmas_on_expr(cross_nested&, nex_sum*);
    
    template <typename T> // T has an iterator of (coeff(), var())
    bool row_has_monomial_to_refine(const T&) const;
    lpvar find_term_column(const lp::lar_term &, rational & a) const;
    static lp::lar_term expression_to_normalized_term(const nex_sum*, rational& a, rational & b);
    static void add_linear_to_vector(const nex*, vector<std::pair<rational, lpvar>> &);
    static void add_mul_to_vector(const nex_mul*, vector<std::pair<rational, lpvar>> &);
    bool interval_from_term_with_deps(const nex* e, interv&) const;
    const nex* get_zero_interval_child(const nex_mul*) const;
    const nex* get_inf_interval_child(const nex_sum*) const;
    bool has_zero_interval(const nex* ) const;
    bool has_inf_interval(const nex* ) const;    
    bool mul_has_inf_interval(const nex_mul* ) const;
    bool check_cross_nested_expr(const nex*);
}; // end of horner
}
