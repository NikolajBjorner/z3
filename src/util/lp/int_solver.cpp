/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
namespace lean {

void int_solver::fix_non_base_columns() {
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
            display_column(tout, v);
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

int int_solver::find_inf_int_base_column() {
    if (m_inf_int_set.is_empty())
        return -1;
    int j = find_inf_int_boxed_base_column_with_smallest_range();
    if (j != -1)
        return j;
    unsigned k = settings().random_next() % m_inf_int_set.m_index.size();
    return m_inf_int_set.m_index[k];
}

int int_solver::find_inf_int_boxed_base_column_with_smallest_range() {
    int result = -1;
    mpq range;
    mpq new_range;
    mpq small_range_thresold(1024);
    unsigned n = 0;
    lar_core_solver & lcs = m_lar_solver->m_mpq_lar_core_solver;

    for (int j : m_inf_int_set.m_index) {
        lean_assert(is_base(j) && column_is_int_inf(j));
        if (!is_boxed(j))
            continue;
        new_range  = lcs.m_r_upper_bounds()[j].x - lcs.m_r_low_bounds()[j].x;
        if (new_range > small_range_thresold) 
            continue;
        if (result == -1) {
            result = j;
            range  = new_range;
            n      = 1;
            continue;
        }
        if (new_range < range) {
            n      = 1;
            result = j;
            range  = new_range;
            continue;
        }
        if (new_range == range) {
            n++;
            if (settings().random_next() % n == 0) {
                result = j;
                continue;
            }
        }
    }
    return result;
    
}

bool int_solver::mk_gomory_cut(unsigned row_index, explanation & ex) {
    lean_assert(false);
    return true;
    /*
    const auto & row = m_lar_solver->A_r().m_rows[row_index];
            // The following assertion is wrong. It may be violated in mixed-integer problems.
    // SASSERT(!all_coeff_int(r));
    theory_var x_i = r.get_base_var();
        
    SASSERT(is_int(x_i));
    // The following assertion is wrong. It may be violated in mixed-real-interger problems.
    // The check is_gomory_cut_target will discard rows where any variable contains infinitesimals.
    // SASSERT(m_value[x_i].is_rational()); // infinitesimals are not used for integer variables
    SASSERT(!m_value[x_i].is_int());     // the base variable is not assigned to an integer value.

    if (constrain_free_vars(r) || !is_gomory_cut_target(r)) {
        TRACE("gomory_cut", tout << "failed to apply gomory cut:\n";
              tout << "constrain_free_vars(r):  " << constrain_free_vars(r) << "\n";);
        return false;
    }

    TRACE("gomory_cut", tout << "applying cut at:\n"; display_row_info(tout, r););
        
    antecedents ante(*this);

    m_stats.m_gomory_cuts++;

    // gomory will be   pol >= k
    numeral k(1);
    buffer<row_entry> pol;
        
    numeral f_0  = Ext::fractional_part(m_value[x_i]);
    numeral one_minus_f_0 = numeral(1) - f_0; 
    SASSERT(!f_0.is_zero());
    SASSERT(!one_minus_f_0.is_zero());
        
    numeral lcm_den(1);
    unsigned num_ints = 0;

    typename vector<row_entry>::const_iterator it  = r.begin_entries();
    typename vector<row_entry>::const_iterator end = r.end_entries();
    for (; it != end; ++it) {
        if (!it->is_dead() && it->m_var != x_i) {
            theory_var x_j   = it->m_var;
            numeral a_ij = it->m_coeff;
            a_ij.neg();  // make the used format compatible with the format used in: Integrating Simplex with DPLL(T)
            if (is_real(x_j)) {
                numeral new_a_ij;
                if (at_lower(x_j)) {
                    if (a_ij.is_pos()) {
                        new_a_ij  =  a_ij / one_minus_f_0;
                    }
                    else {
                        new_a_ij  =  a_ij / f_0;
                        new_a_ij.neg();
                    }
                    k.addmul(new_a_ij, lower_bound(x_j).get_rational());
                    lower(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                }
                else {
                    SASSERT(at_upper(x_j));
                    if (a_ij.is_pos()) {
                        new_a_ij =   a_ij / f_0; 
                        new_a_ij.neg(); // the upper terms are inverted.
                    }
                    else {
                        new_a_ij =   a_ij / one_minus_f_0; 
                    }
                    k.addmul(new_a_ij, upper_bound(x_j).get_rational());
                    upper(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                }
                TRACE("gomory_cut_detail", tout << a_ij << "*v" << x_j << " k: " << k << "\n";);
                pol.push_back(row_entry(new_a_ij, x_j));
            }
            else {
                ++num_ints;
                SASSERT(is_int(x_j));
                numeral f_j = Ext::fractional_part(a_ij);
                TRACE("gomory_cut_detail", 
                      tout << a_ij << "*v" << x_j << "\n";
                      tout << "fractional_part: " << Ext::fractional_part(a_ij) << "\n";
                      tout << "f_j: " << f_j << "\n";
                      tout << "f_0: " << f_0 << "\n";
                      tout << "one_minus_f_0: " << one_minus_f_0 << "\n";);
                if (!f_j.is_zero()) {
                    numeral new_a_ij;
                    if (at_lower(x_j)) {
                        if (f_j <= one_minus_f_0) {
                            new_a_ij = f_j / one_minus_f_0;
                        }
                        else {
                            new_a_ij = (numeral(1) - f_j) / f_0;
                        }
                        k.addmul(new_a_ij, lower_bound(x_j).get_rational());
                        lower(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                    }
                    else {
                        SASSERT(at_upper(x_j));
                        if (f_j <= f_0) {
                            new_a_ij = f_j / f_0;
                        }
                        else {
                            new_a_ij = (numeral(1) - f_j) / one_minus_f_0;
                        }
                        new_a_ij.neg(); // the upper terms are inverted
                        k.addmul(new_a_ij, upper_bound(x_j).get_rational());
                        upper(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                    }
                    TRACE("gomory_cut_detail", tout << "new_a_ij: " << new_a_ij << " k: " << k << "\n";);
                    pol.push_back(row_entry(new_a_ij, x_j));
                    lcm_den = lcm(lcm_den, denominator(new_a_ij));
                }
            }
        }
    }

    CTRACE("empty_pol", pol.empty(), display_row_info(tout, r););

    expr_ref bound(get_manager());
    if (pol.empty()) {
        SASSERT(k.is_pos());
        // conflict 0 >= k where k is positive
        set_conflict(ante, ante, "gomory-cut");
        return true;
    }
    else if (pol.size() == 1) {
        theory_var v = pol[0].m_var;
        k /= pol[0].m_coeff;
        bool is_lower = pol[0].m_coeff.is_pos();
        if (is_int(v) && !k.is_int()) {
            k = is_lower?ceil(k):floor(k);
        }
        rational _k = k.to_rational();
        if (is_lower)
            bound = m_util.mk_ge(get_enode(v)->get_owner(), m_util.mk_numeral(_k, is_int(v)));
        else
            bound = m_util.mk_le(get_enode(v)->get_owner(), m_util.mk_numeral(_k, is_int(v)));
    }
    else { 
        if (num_ints > 0) {
            lcm_den = lcm(lcm_den, denominator(k));
            TRACE("gomory_cut_detail", tout << "k: " << k << " lcm_den: " << lcm_den << "\n";
                  for (unsigned i = 0; i < pol.size(); i++) {
                      tout << pol[i].m_coeff << " " << pol[i].m_var << "\n";
                  }
                  tout << "k: " << k << "\n";);
            SASSERT(lcm_den.is_pos());
            if (!lcm_den.is_one()) {
                // normalize coefficients of integer parameters to be integers.
                unsigned n = pol.size();
                for (unsigned i = 0; i < n; i++) {
                    pol[i].m_coeff *= lcm_den;
                    SASSERT(!is_int(pol[i].m_var) || pol[i].m_coeff.is_int());
                }
                k *= lcm_den;
            }
            TRACE("gomory_cut_detail", tout << "after *lcm\n";
                  for (unsigned i = 0; i < pol.size(); i++) {
                      tout << pol[i].m_coeff << " * v" << pol[i].m_var << "\n";
                  }
                  tout << "k: " << k << "\n";);
        }
        mk_polynomial_ge(pol.size(), pol.c_ptr(), k.to_rational(), bound);            
    }
    TRACE("gomory_cut", tout << "new cut:\n" << bound << "\n"; ante.display(tout););
    literal l     = null_literal;
    context & ctx = get_context();
    ctx.internalize(bound, true);
    l = ctx.get_literal(bound);
    ctx.mark_as_relevant(l);
    dump_lemmas(l, ante);
    ctx.assign(l, ctx.mk_justification(
                                       gomory_cut_justification(
                                                                get_id(), ctx.get_region(), 
                                                                ante.lits().size(), ante.lits().c_ptr(), 
                                                                ante.eqs().size(), ante.eqs().c_ptr(), ante, l)));
    return true;
    */

}
lia_move int_solver::check(lar_term& t, mpq& k, explanation& ex) {
    lean_assert(is_feasible());
    init_inf_int_set();
    lean_assert(inf_int_set_is_correct());
    // currently it is a reimplementation of
    // final_check_status theory_arith<Ext>::check_int_feasibility()
    // from theory_arith_int.h
	if (m_lar_solver->model_is_int_feasible())
		return lia_move::ok;
    if (!gcd_test(ex))
        return lia_move::conflict;
    /*
      if (m_params.m_arith_euclidean_solver)
            apply_euclidean_solver();
        
    */
    m_lar_solver->pivot_fixed_vars_from_basis();
    patch_int_infeasible_columns();
    fix_non_base_columns();
    lean_assert(is_feasible());
    TRACE("arith_int_rows", trace_inf_rows(););
    
    if (find_inf_int_base_column() == -1)
        return lia_move::ok;
        

    if ((++m_branch_cut_counter) % settings().m_int_branch_cut_threshold == 0) {
        move_non_base_vars_to_bounds();
        lp_status st = m_lar_solver->find_feasible_solution();
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            return lia_move::give_up;
        }
        int j = find_inf_int_base_column();
        if (j != -1) {
            TRACE("arith_int", tout << "j = " << j << " does not have an integer assignment: " << get_value(j) << "\n";);
            unsigned row_index = m_lar_solver->m_mpq_lar_core_solver.m_r_heading[j];
            if (!mk_gomory_cut(row_index, ex)) {
                return lia_move::give_up;
                // silent failure
            }
            return lia_move::cut;
        }
    }
    else {
        int j = find_inf_int_base_column();
        if (j != -1) {
            TRACE("arith_int", tout << "j" << j << " does not have an integer assignment: " << get_value(j) << "\n";);
            lean_assert(t.is_empty());
            t.add_to_map(j, mpq(1));
            k = floor(get_value(j));
            return lia_move::branch;
        }
    }
    //    return true;
    return lia_move::give_up;
}

void int_solver::move_non_base_vars_to_bounds() {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    for (unsigned j : lcs.m_r_nbasis) {
        auto & val = lcs.m_r_x[j];
        switch (lcs.m_column_types()[j]) {
        case column_type::boxed:
            if (val != lcs.m_r_low_bounds()[j] && val != lcs.m_r_upper_bounds()[j])
                set_value(j, lcs.m_r_low_bounds()[j]);
            break;
        case column_type::low_bound:
            if (val != lcs.m_r_low_bounds()[j])
                set_value(j, lcs.m_r_low_bounds()[j]);
            break;
        case column_type::upper_bound:
            if (val != lcs.m_r_upper_bounds()[j])
                set_value(j, lcs.m_r_upper_bounds()[j]);
            break;
        default:
            if (is_int(j) && !val.is_int()) {
                set_value(j, impq(floor(val)));
            }
        }
    }
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
    
bool int_solver::gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i, explanation & ex) {
    iterator_on_row<mpq> it(A.m_rows[i]);
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
            fill_explanation_from_fixed_columns(it, ex);
        
        if (least_coeff.is_one() && !least_coeff_is_bounded) {
            SASSERT(gcds.is_one());
            return true;
        }
        
        if (least_coeff_is_bounded) {
            return ext_gcd_test(it, least_coeff, lcm_den, consts, ex);
        }
        return true;
}

void int_solver::add_to_explanation_from_fixed_or_boxed_column(unsigned j, explanation & ex) {
    constraint_index lc, uc;
    m_lar_solver->get_bound_constraint_witnesses_for_column(j, lc, uc);
    ex.m_explanation.push_back(std::make_pair(mpq(1), lc));
    ex.m_explanation.push_back(std::make_pair(mpq(1), uc));
}
void int_solver::fill_explanation_from_fixed_columns(iterator_on_row<mpq> & it, explanation & ex) {
    it.reset();
    unsigned j;
    while (it.next(j)) {
        if (!m_lar_solver->column_is_fixed(j))
            continue;
        add_to_explanation_from_fixed_or_boxed_column(j, ex);
    }
}
    
bool int_solver::gcd_test(explanation & ex) {
	auto & A = m_lar_solver->A_r(); // getting the matrix
	for (unsigned i = 0; i < A.row_count(); i++)
        if (!gcd_test_for_row(A, i, ex)) {
            std::cout << "false from gcd_test\n" ;
            return false;
        }
        
	return true;
}

bool int_solver::ext_gcd_test(iterator_on_row<mpq> & it,
                              mpq const & least_coeff, 
                              mpq const & lcm_den,
                              mpq const & consts, explanation& ex) {
    mpq gcds(0);
    mpq l(consts);
    mpq u(consts);

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
            add_to_explanation_from_fixed_or_boxed_column(j, ex);
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
        fill_explanation_from_fixed_columns(it, ex);
        return false;
    }
        
    return true;

}

linear_combination_iterator<mpq> * int_solver::get_column_iterator(unsigned j) {
    if (m_lar_solver->use_tableau())
        return new iterator_on_column<mpq, impq>(m_lar_solver->A_r().m_columns[j], m_lar_solver->A_r());
   return new iterator_on_indexed_vector<mpq>(m_lar_solver->get_column_in_lu_mode(j));
}


int_solver::int_solver(lar_solver* lar_slv) :
    m_lar_solver(lar_slv),
    m_branch_cut_counter(0) {
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

void int_solver::display_column(std::ostream & out, unsigned j) const {
    m_lar_solver->m_mpq_lar_core_solver.m_r_solver.print_column_info(j, out);
}

bool int_solver::inf_int_set_is_correct() const {
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

bool int_solver::is_base(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_heading[j] >= 0;
}

bool int_solver::is_boxed(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_column_types[j] == column_type::boxed;
}

lp_settings& int_solver::settings() {
    return m_lar_solver->settings();
}

}
