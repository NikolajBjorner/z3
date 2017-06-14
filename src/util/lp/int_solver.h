/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/lp_settings.h"
#include "util/lp/static_matrix.h"
#include "util/lp/iterator_on_row.h"

namespace lean {
class lar_solver;
template <typename T, typename X>
struct lp_constraint;

class int_solver {
public:
    lar_solver *m_lar_solver;
    vector<std::pair<mpq, constraint_index>> m_explanation;
    int_solver(lar_solver* lp);
    bool check();// main function to check that solution provided by lar_solver is valid for integral values or can be adjusted.
private:

    // how to tighten bounds for integer variables.

    bool gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i); 
    
    // gcd test
    // 5*x + 3*y + 6*z = 5
    // suppose x is fixed at 2.
    // so we have 10 + 3(y + 2z) = 5
    //             5 = -3(y + 2z)
    // this is unsolvable because 5/3 is not an integer.
    // so we create a lemma that rules out this condition.
    // 
    bool gcd_test(); // returns false in case of failure. Creates a theory lemma in case of failure.

    // create goromy cuts
    // either creates a conflict or a bound.

    // branch and bound: 
    // decide what to branch and bound on
    // creates a fresh inequality.

    bool branch(const lp_constraint<mpq, mpq> & new_inequality);
    bool ext_gcd_test(iterator_on_row<mpq> & it,
                      mpq const & least_coeff, 
                      mpq const & lcm_den,
                      mpq const & consts);
    void fill_explanation_from_fixed_columns(iterator_on_row<mpq> & it);
    void add_to_explanation_from_fixed_or_boxed_column(unsigned j);
    
};
}
