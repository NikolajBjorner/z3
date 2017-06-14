/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
namespace lean {

bool int_solver::check() {
    // currently it is a reimplementation of
    // final_check_status theory_arith<Ext>::check_int_feasibility()
    // from theory_arith_int.h
	if (m_lar_solver->model_is_int_feasible())
		return true;
    if (!gcd_test())
        return false;
    /*
      if (m_params.m_arith_euclidean_solver)
            apply_euclidean_solver();
        
    */
    m_lar_solver->pivot_fixed_vars_from_basis();
    return false;
}

mpq get_denominators_lcm(iterator_on_row<mpq> &it) {
    mpq r(1);
    mpq a;
    unsigned j;
    while (it.next(a, j)) {
        r = lcm(r, denominator(a));
    }
    return r;
}
    
bool int_solver::gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i) {
    iterator_on_row<mpq> it(A.m_rows[i]);
    std::cout << "gcd_test_for_row(" << i << ")\n";
    mpq lcm_den = get_denominators_lcm(it);
    mpq consts(0);
    mpq gcds(0);
    mpq least_coeff(0);
    bool    least_coeff_is_bounded = false;
    mpq a;
    unsigned j;
    while (it.next(a, j)) {
            if (m_lar_solver->column_is_fixed(j)) {
                mpq aux = lcm_den * a;
                consts += aux * m_lar_solver->column_low_bound(j).x;
            }
            else if (m_lar_solver->column_is_real(j)) {
                return true;
            }
            else if (gcds.is_zero()) {
                gcds = abs(lcm_den * a);
                least_coeff = gcds;
                least_coeff_is_bounded = m_lar_solver->column_is_bounded(j);
            }
            else {
                mpq aux = abs(lcm_den * a);
                gcds = gcd(gcds, aux);
                if (aux < least_coeff) {
                    least_coeff = aux;
                    least_coeff_is_bounded = m_lar_solver->column_is_bounded(j);
                }
                else if (least_coeff_is_bounded && aux == least_coeff) {
                    least_coeff_is_bounded = m_lar_solver->column_is_bounded(j);
                }
            }
            SASSERT(gcds.is_int());
            SASSERT(least_coeff.is_int());
            TRACE("gcd_test_bug", tout << "coeff: " << a << ", gcds: " << gcds 
                  << " least_coeff: " << least_coeff << " consts: " << consts << "\n";);
        
        }
    
        if (gcds.is_zero()) {
            // All variables are fixed.
            // This theory guarantees that the assignment satisfies each row, and
            // fixed integer variables are assigned to integer values.
            return true;
        }
        
        if (!(consts / gcds).is_int())
            fill_explanation_from_fixed_columns(it);
        
        if (least_coeff.is_one() && !least_coeff_is_bounded) {
            SASSERT(gcds.is_one());
            return true;
        }
        
        if (least_coeff_is_bounded) {
            return ext_gcd_test(it, least_coeff, lcm_den, consts);
        }
        return true;
}

void int_solver::add_to_explanation_from_fixed_or_boxed_column(unsigned j) {
    constraint_index lc, uc;
    m_lar_solver->get_bound_constraint_witnesses_for_column(j, lc, uc);
    m_explanation.push_back(std::make_pair(mpq(1), lc));
    m_explanation.push_back(std::make_pair(mpq(1), uc));
}
void int_solver::fill_explanation_from_fixed_columns(iterator_on_row<mpq> & it) {
    it.reset();
    unsigned j;
    while (it.next(j)) {
        if (!m_lar_solver->column_is_fixed(j))
            continue;
        add_to_explanation_from_fixed_or_boxed_column(j);
    }
}
    
bool int_solver::gcd_test() {
	auto & A = m_lar_solver->A_r(); // getting the matrix
	for (unsigned i = 0; i < A.row_count(); i++)
        if (!gcd_test_for_row(A, i)) {
            std::cout << "false from gcd_test\n" ;
            return false;
        }
        
	return true;
}

bool int_solver::ext_gcd_test(iterator_on_row<mpq> & it,
                              mpq const & least_coeff, 
                              mpq const & lcm_den,
                              mpq const & consts) {

    std::cout << "calling ext_gcd_test" << std::endl;
    mpq gcds(0);
    mpq l(consts);
    mpq u(consts);
    m_explanation.clear();

    it.reset();
    mpq a;
    unsigned j;
    while (it.next(a, j)) {
        if (m_lar_solver->column_is_fixed(j))
            continue;
        SASSERT(!m_lar_solver->column_is_real(j));
        mpq ncoeff = lcm_den * a;
        SASSERT(ncoeff.is_int());
        mpq abs_ncoeff = abs(ncoeff);
        if (abs_ncoeff == least_coeff) {
            SASSERT(m_lar_solver->column_is_bounded(j));
            if (ncoeff.is_pos()) {
                // l += ncoeff * m_lar_solver->column_low_bound(j).x;
                l.addmul(ncoeff, m_lar_solver->column_low_bound(j).x);
                // u += ncoeff * m_lar_solver->column_upper_bound(j).x;
                u.addmul(ncoeff, m_lar_solver->column_upper_bound(j).x);
            }
            else {
                // l += ncoeff * upper_bound(j).get_rational();
                l.addmul(ncoeff, m_lar_solver->column_upper_bound(j).x);
                // u += ncoeff * lower_bound(j).get_rational();
                u.addmul(ncoeff, m_lar_solver->column_low_bound(j).x);
            }
            add_to_explanation_from_fixed_or_boxed_column(j);
        }
        else if (gcds.is_zero()) {
            gcds = abs_ncoeff; 
        }
        else {
            gcds = gcd(gcds, abs_ncoeff);
        }
        SASSERT(gcds.is_int());
    }
        
    if (gcds.is_zero()) {
        return true;
    }
        
    mpq l1 = ceil(l/gcds);
    mpq u1 = floor(u/gcds);
        
    if (u1 < l1) {
        fill_explanation_from_fixed_columns(it);
        return false;
    }
        
    return true;

}
    
int_solver::int_solver(lar_solver* lar_slv) : m_lar_solver(lar_slv) {}

}
