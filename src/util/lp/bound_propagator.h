/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include "util/lp/bound_evidence.h"
namespace lean {
    class lar_solver; // forward definition;
    template <typename T, typename X> class lar_core_solver; // forward definition

class bound_propagator {
    unsigned m_row_index;
    lar_solver & m_solver;
    lar_core_solver<mpq, numeric_pair<mpq>>& m_core_solver;
    std::vector<bound_evidence> & m_bound_evidences;
        // We have the equality, sum by j of pivot_row[j]*x[j] + x[basis[j]] = 0
        // We try to pin a var by pushing the total of the partial sum down, denoting the variable of this process by _minus.
        // In the same loop trying to pin a var by pushing the partial sum up, denoting it by _plus
    int m_cand_minus = -1;  // the variable pinned from above
    mpq m_a_minus; // the coefficent before the minus candidate
    unsigned m_n_minus = 0; // the number of terms active, limiting from above found so far
    numeric_pair<mpq> m_bound_minus = numeric_pair<mpq>(0, 0);
    bool m_interested_in_minus = true; // the partial sum for min, seen so far
    int m_cand_plus = -1;
    mpq m_a_plus; // the coefficent before the plus candidate
    unsigned m_n_plus = 0; // the number of terms limiting, active, from below found so far
    numeric_pair<mpq> m_bound_plus = numeric_pair<mpq>(0, 0); // the partial sum for plus, seen so far
    bool m_interested_in_plus = true;
public :
    // constructor
    bound_propagator(unsigned row_index, lar_solver & solver, std::vector<bound_evidence> & bound_evidences);// : m_row_index(row_index), m_solver(solver), m_bound_evidences(bound_evidences), m_core_solver(solver.m_mpq_lar_core_solver) {}

    void propagate();
    void propagate_bound_on_var_on_coeff(int j, const mpq &a);
    void propagate_for_minus();
    void propagate_for_plus();
    void propagate_bound_on_pivot_row_one_var_case_boxed_fixed(int j, const mpq & a);
    void propagate_bound_on_pivot_row_one_var_case_low_upper(const mpq& a,
                                                             int sign, // sign > 0 means the term can grow, sign < 0 means term can decrease
                                                             int j);

    void fill_bound_evidence_plus(bound_evidence & bnd_evid);
    void fill_bound_evidence_minus(bound_evidence & bnd_evid);
    void fill_bound_evidence_sign_on_coeff(int sign, unsigned j, const mpq & a, bound_evidence & be);
    void fill_bound_kind_plus_on_pos(bound_evidence & be);
    void fill_bound_kind_plus_on_neg(bound_evidence & be);
    void fill_bound_kind_minus_on_pos(bound_evidence & be);
    void fill_bound_kind_minus_on_neg(bound_evidence & be);
};
}
