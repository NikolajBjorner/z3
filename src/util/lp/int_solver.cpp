/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
namespace lean {

void int_solver::fix_non_base_vars() {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    for (unsigned j : lcs.m_r_nbasis) {
        if (column_is_int_inf(j)) {
            set_value(j, floor(lcs.m_r_x[j].x));
        }
    }
    if (m_lar_solver->find_feasible_solution() == INFEASIBLE)
        failed();
}

void int_solver::failed() {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    
    for (unsigned j : m_old_values_set.m_index) {
        lcs.m_r_x[j] = m_old_values_data[j];
        lean_assert(lcs.m_r_solver.column_is_feasible(j));
        lcs.m_r_solver.remove_column_from_inf_set(j);
    }
    lean_assert(lcs.m_r_solver.calc_current_x_is_feasible_include_non_basis());
    lean_assert(lcs.m_r_solver.current_x_is_feasible());
    m_old_values_set.clear();
}

void int_solver::trace_inf_rows() const {
    unsigned num = m_lar_solver->A_r().column_count();
    for (unsigned v = 0; v < num; v++) {
        if (is_int(v) && !get_value(v).is_int()) {
            display_var(tout, v);
        }
    }
    
    num = 0;
    for (unsigned i = 0; i < m_lar_solver->A_r().row_count(); i++) {
        unsigned j = m_lar_solver->m_mpq_lar_core_solver.m_r_basis[i];
        if (column_is_int_inf(j)) {
            num++;
            iterator_on_row<mpq> it(m_lar_solver->A_r().m_rows[i]);
            m_lar_solver->print_linear_iterator(&it, tout);
            tout << "\n";
        }
    }
    tout << "num of int infeasible: " << num << "\n";
}
    
bool int_solver::check() {
    lean_assert(is_feasible());
    init_inf_int_set();
    lean_assert(inf_int_set_is_correct());
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
    patch_int_infeasible_columns();
    fix_non_base_vars();
    lean_assert(is_feasible());
    TRACE("arith_int_rows", trace_inf_rows(););

    
        /*    
        theory_var int_var = find_infeasible_int_base_var();
        if (int_var == null_theory_var) {
            TRACE("arith_int_incomp", tout << "FC_DONE 2...\n"; display(tout););
            return m_liberal_final_check || !m_changed_assignment ? FC_DONE : FC_CONTINUE;
        }
        
#if 0
        if (find_bounded_infeasible_int_base_var() == null_theory_var) {
            // TODO: this is too expensive... I should replace it by a procedure
            // that refine bounds using the current state of the tableau.
            if (!max_min_infeasible_int_vars())
                return FC_CONTINUE;
            if (!gcd_test())
                return FC_CONTINUE;
        }
#endif 

        m_branch_cut_counter++;
        // TODO: add giveup code
        if (m_branch_cut_counter % m_params.m_arith_branch_cut_ratio == 0) {
            TRACE("opt_verbose", display(tout););
            move_non_base_vars_to_bounds();
            if (!make_feasible()) {
                TRACE("arith_int", tout << "failed to move variables to bounds.\n";);
                failed();
                return FC_CONTINUE;
            }
            theory_var int_var = find_infeasible_int_base_var();
            if (int_var != null_theory_var) {
                TRACE("arith_int", tout << "v" << int_var << " does not have an integer assignment: " << get_value(int_var) << "\n";);
                SASSERT(is_base(int_var));
                row const & r = m_rows[get_var_row(int_var)];
                if (!mk_gomory_cut(r)) {
                    // silent failure
                }
                return FC_CONTINUE;
            }
        }
        else {
            if (m_params.m_arith_int_eq_branching && branch_infeasible_int_equality()) {
                return FC_CONTINUE;
            }

            theory_var int_var = find_infeasible_int_base_var();
            if (int_var != null_theory_var) {
                TRACE("arith_int", tout << "v" << int_var << " does not have an integer assignment: " << get_value(int_var) << "\n";);
                // apply branching 
                branch_infeasible_int_var(int_var);
                return FC_CONTINUE;
            }
        }
        return m_liberal_final_check || !m_changed_assignment ? FC_DONE : FC_CONTINUE;

     */
    return false;
}

void int_solver::set_value(unsigned j, const impq & new_val) {
    auto & x = m_lar_solver->m_mpq_lar_core_solver.m_r_x[j];
    if (!m_old_values_set.contains(j)) {
        m_old_values_set.insert(j);
        m_old_values_data[j] = x;
    }
    auto delta = new_val - x;
    x = new_val;
    m_lar_solver->change_basic_x_by_delta_on_column(j, delta);
    update_column_in_inf_set_set(j);
}

void int_solver::patch_int_infeasible_columns() {
    bool inf_l, inf_u;
    impq l, u;
    mpq m;
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    for (unsigned j : lcs.m_r_nbasis) {
        if (!is_int(j))
            continue;
        get_freedom_interval_for_column(j, inf_l, l, inf_u, u, m);
        impq & val = lcs.m_r_x[j];
        bool val_is_int = val.is_int();
        bool m_is_one = m.is_one();
        if (m.is_one() && val_is_int)
            continue;
        // check whether value of j is already a multiple of m.
        if (val_is_int && (val.x / m).is_int())
            continue;
        TRACE("patch_int",
              tout << "TARGET j" << j << " -> [";
              if (inf_l) tout << "-oo"; else tout << l;
              tout << ", ";
              if (inf_u) tout << "oo"; else tout << u;
              tout << "]";
              tout << ", m: " << m << ", val: " << val << ", is_int: " << m_lar_solver->column_is_int(j) << "\n";);
        if (!inf_l) {
            l = m_is_one? ceil(l) : m * ceil(l / m);
            if (inf_u || l <= u) {
                TRACE("patch_int",
                      tout << "patching with l: " << l << '\n';);
                
                set_value(j, l);
            } else {
                TRACE("patch_int", 
                      tout << "not patching " << l << "\n";);
            }
        } else if (!inf_u) {
            u = m_is_one? floor(u) : m * floor(u / m);
            set_value(j, u);
            TRACE("patch_int",
                  tout << "patching with u: " << u << '\n';);
        } else {
            set_value(j, impq(0));
            TRACE("patch_int",
                  tout << "patching with 0\n";);
        }
    }
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

linear_combination_iterator<mpq> * int_solver::get_column_iterator(unsigned j) {
    if (m_lar_solver->use_tableau())
        return new iterator_on_column<mpq, impq>(m_lar_solver->A_r().m_columns[j], m_lar_solver->A_r());
   return new iterator_on_indexed_vector<mpq>(m_lar_solver->get_column_in_lu_mode(j));
}


int_solver::int_solver(lar_solver* lar_slv) : m_lar_solver(lar_slv) {
    lean_assert(m_old_values_set.size() == 0);
    m_old_values_set.resize(lar_slv->A_r().column_count());
    m_old_values_data.resize(lar_slv->A_r().column_count(), zero_of_type<impq>());    
}

bool int_solver::lower(unsigned j) const {
    switch (m_lar_solver->m_mpq_lar_core_solver.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::low_bound:
        return true;
    default:
        return false;
    }
}

bool int_solver::upper(unsigned j) const {
    switch (m_lar_solver->m_mpq_lar_core_solver.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::upper_bound:
        return true;
    default:
        return false;
    }
}

const impq& int_solver::lower_bound(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_low_bounds()[j];
}

const impq& int_solver::upper_bound(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_upper_bounds()[j];
}


void set_lower(impq & l,
               bool & inf_l,
               impq const & v ) {
    if (inf_l || v > l) {
        l = v;
        inf_l = false;
    }
}

void set_upper(impq & u,
               bool & inf_u,
               impq const & v) {
    if (inf_u || v < u) {
        u = v;
        inf_u = false;
    }
}

bool int_solver::get_freedom_interval_for_column(unsigned x_j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m) {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    if (lcs.m_r_heading[x_j] >= 0) // the basic var 
        return false;

    impq const & x_j_val = lcs.m_r_x[x_j];
    linear_combination_iterator<mpq> *it = get_column_iterator(x_j);

    inf_l = true;
    inf_u = true;
    l = u = zero_of_type<impq>();
    m = mpq(1);

    if (lower(x_j)) {
        set_lower(l, inf_l, lower_bound(x_j));
    }
    if (upper(x_j)) {
        set_upper(u, inf_u, upper_bound(x_j));
    }

    mpq a_ij; unsigned i;
    while (it->next(a_ij, i)) {
        unsigned x_i = lcs.m_r_basis[i];
        impq const & x_i_val = lcs.m_r_x[x_i];
        if (is_int(x_i) && is_int(x_j) && !a_ij.is_int())
            m = lcm(m, denominator(a_ij));
        bool x_i_lower = lower(x_i);
        bool x_i_upper = upper(x_i);
        if (a_ij.is_neg()) {
            if (x_i_lower) {
                impq new_l = x_j_val + ((x_i_val - lcs.m_r_low_bounds()[x_i]) / a_ij);
                set_lower(l, inf_l, new_l);
                if (!inf_l && !inf_u && l == u) break;;                
            }
            if (x_i_upper) {
                impq new_u = x_j_val + ((x_i_val - lcs.m_r_upper_bounds()[x_i]) / a_ij);
                set_upper(u, inf_u, new_u);
                if (!inf_l && !inf_u && l == u) break;;                
            }
        }
        else {
            if (x_i_upper) {
                impq new_l = x_j_val + ((x_i_val - lcs.m_r_upper_bounds()[x_i]) / a_ij);
                set_lower(l, inf_u, new_l);
                if (!inf_l && !inf_u && l == u) break;;                
            }
            if (x_i_lower) {
                impq new_u = x_j_val + ((x_i_val - lcs.m_r_low_bounds()[x_i]) / a_ij);
                set_upper(u, inf_u, new_u);
                if (!inf_l && !inf_u && l == u) break;;                
            }
        }
    }

    delete it;
    TRACE("freedom_interval",
          tout << "freedom variable for:\n";
          tout << m_lar_solver->get_column_name(x_j);
          tout << "[";
          if (inf_l) tout << "-oo"; else tout << l;
          tout << "; ";
          if (inf_u) tout << "oo";  else tout << u;
          tout << "]\n";);
    return true;

}

bool int_solver::is_int(unsigned j) const {
    return m_lar_solver->column_is_int(j);
}

bool int_solver::value_is_int(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_x[j].is_int();
}

    

bool int_solver::is_feasible() const {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    lean_assert(
                lcs.m_r_solver.calc_current_x_is_feasible_include_non_basis() ==
                lcs.m_r_solver.current_x_is_feasible());
    return lcs.m_r_solver.current_x_is_feasible();
}
const impq & int_solver::get_value(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_x[j];
}

void int_solver::display_var(std::ostream & out, unsigned j) const {
    m_lar_solver->m_mpq_lar_core_solver.m_r_solver.print_column_info(j, out);
}

bool int_solver::inf_int_set_is_correct() const {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    for (unsigned j = 0; j < m_lar_solver->A_r().column_count(); j++) {
        if (m_inf_int_set.contains(j) != is_int(j) && (!value_is_int(j)))
            return false;
    }
    return true;
}

bool int_solver::column_is_int_inf(unsigned j) const {
    return is_int(j) && (!value_is_int(j));
}
    
void int_solver::init_inf_int_set() {
    m_inf_int_set.clear();
    m_inf_int_set.resize(m_lar_solver->A_r().column_count());
    for (unsigned j : m_lar_solver->m_mpq_lar_core_solver.m_r_basis) {
        if (column_is_int_inf(j))
            m_inf_int_set.insert(j);
    }
}

void int_solver::update_column_in_inf_set_set(unsigned j) {
    if (is_int(j) && (!value_is_int(j)))
        m_inf_int_set.insert(j);
    else
        m_inf_int_set.erase(j);
}
    
}
