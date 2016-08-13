/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <string>
#include <algorithm>
#include <vector>
#include <utility>
#include "util/lp/lar_solver.h"
#include "util/lp/random_updater.h"
namespace lean {
double conversion_helper <double>::get_low_bound(const column_info<mpq> & ci) {
    if (!ci.low_bound_is_strict())
        return ci.get_low_bound().get_double();
    double eps = 0.00001;
    if (!ci.upper_bound_is_set())
        return ci.get_low_bound().get_double() + eps;
    eps = std::min((ci.get_upper_bound() - ci.get_low_bound()).get_double() / 1000, eps);
    return ci.get_low_bound().get_double() + eps;
}

double conversion_helper <double>::get_upper_bound(const column_info<mpq> & ci) {
    if (!ci.upper_bound_is_strict())
        return ci.get_upper_bound().get_double();
    double eps = 0.00001;
    if (!ci.low_bound_is_set())
        return ci.get_upper_bound().get_double() - eps;
    eps = std::min((ci.get_upper_bound() - ci.get_low_bound()).get_double() / 1000, eps);
    return ci.get_upper_bound().get_double() - eps;
}

canonic_left_side lar_solver::create_or_fetch_existing_left_side(const std::vector<std::pair<mpq, var_index>>& left_side_par) {
    auto left_side = canonic_left_side(left_side_par);
    lean_assert(left_side.size() > 0);
    if (!m_map_of_canonic_left_sides.contains(left_side)) {
        var_index j = A().column_count();
        A().add_column();
        ul_pair ul(j);
        m_map_of_canonic_left_sides[left_side] = ul;
        auto ci_cls = column_info_with_cls(left_side);
        ci_cls.m_column_info.set_name("_s" + T_to_string(j));
        ci_cls.m_column_info.set_column_index(j);
        m_map_from_var_index_to_column_info_with_cls[j] = ci_cls;
        add_row_to_A(left_side);
    }
    return left_side;
}

void lar_solver::add_row_to_A(const canonic_left_side & ls) {
    A().add_row();
    fill_row_of_A(A(), ls);
}

mpq lar_solver::find_ratio_of_original_constraint_to_normalized(const canonic_left_side & ls, const lar_constraint & constraint) {
    lean_assert(ls.m_coeffs.size() > 0);
    auto first_pair = ls.m_coeffs[0];
    lean_assert(first_pair.first == numeric_traits<mpq>::one());
    var_index i = first_pair.second;
    auto it = constraint.m_left_side_map_from_index_to_coefficient.find(i);
    lean_assert(it != constraint.m_left_side_map_from_index_to_coefficient.end());
    return it->second;
}

void lar_solver::map_left_side_to_A_of_core_solver(const canonic_left_side &  left_side, unsigned  j) {
    const ul_pair & ul = m_map_of_canonic_left_sides[left_side];
    var_index additional_var = ul.m_additional_var_index;
    lean_assert(valid_index(additional_var));
    column_info_with_cls ci_cls = m_map_from_var_index_to_column_info_with_cls[additional_var];
    column_info<mpq>& ci = ci_cls.m_column_info;
    lean_assert(!is_valid(ci.get_column_index()));
    lean_assert(left_side.size() > 0); // if size is zero we have an empty row
    m_lar_core_solver_params.m_basis.push_back(j); // j will be a basis column, so we put it into the basis as well
    ci.set_column_index(j);
    m_map_from_var_index_to_column_info_with_cls[additional_var] = ci_cls;
}

// this adds a row to A and set the basis column: -1 in the last column of the row
template <typename U, typename V>
void lar_solver::fill_row_of_A(static_matrix<U, V> & A, const canonic_left_side & ls) {
    lean_assert(A.row_count() > 0);
    lean_assert(A.column_count() > 0);
    unsigned i = A.row_count() - 1;
    for (auto & t : ls.m_coeffs) {
        var_index j = t.second;
        A.set(i, j, convert_struct<U, mpq>::convert(t.first));
    }
    unsigned basis_j = A.column_count() - 1;
    A.set(i, basis_j, -one_of_type<U>());
}

template <typename U, typename V>
void lar_solver::create_matrix_A(static_matrix<U, V> & matr) {
    unsigned m = number_or_nontrivial_left_sides();
    unsigned n = m_map_from_var_index_to_column_info_with_cls.size();
    if (matr.row_count() == m && matr.column_count() == n)
        return;
    matr.init_empty_matrix(m, n);
    copy_from_mpq_matrix(matr);

}

template <typename U, typename V>
void lar_solver::copy_from_mpq_matrix(static_matrix<U, V> & matr) {
    lean_assert(matr.row_count() == A().row_count());
    lean_assert(matr.column_count() == A().column_count());
    for (unsigned i = 0; i < matr.row_count(); i++) {
        for (auto & it : A().m_rows[i]) {
            matr.set(i, it.m_j,  convert_struct<U, mpq>::convert(it.get_val()));
        }
    }
}

void lar_solver::set_upper_bound_for_column_info(constraint_index i, const lar_normalized_constraint & norm_constr) {
    const mpq & v = norm_constr.m_right_side;
    const canonic_left_side & ls = norm_constr.m_canonic_left_side;
    ul_pair ul = m_map_of_canonic_left_sides[ls];
    var_index additional_var_index = ul.m_additional_var_index;
    lean_assert(is_valid(additional_var_index));
    column_info_with_cls ci_cls = m_map_from_var_index_to_column_info_with_cls[additional_var_index];
    column_info<mpq> & ci = ci_cls.m_column_info;
    lean_assert(norm_constr.m_kind == LE || norm_constr.m_kind == LT || norm_constr.m_kind == EQ);
    bool strict = norm_constr.m_kind == LT;
    if (!ci.upper_bound_is_set()) {
        ul.m_upper_bound_witness = i;
        ci.set_upper_bound(v);
        ci.set_upper_bound_strict(strict);
    } else if (ci.get_upper_bound() > v) {
        ci.set_upper_bound(v);
        ul.m_upper_bound_witness = i;
        ci.set_upper_bound_strict(strict);
    } else if (ci.get_upper_bound() == v && strict && ci.upper_bound_is_strict() == false) {
        ul.m_upper_bound_witness = i;
        ci.set_upper_bound_strict(strict);
    }
    m_map_from_var_index_to_column_info_with_cls[additional_var_index] = ci_cls;
    m_map_of_canonic_left_sides[ls] = ul;
    if (ci.is_infeasible()) {
        m_status = INFEASIBLE;
        m_infeasible_canonic_left_side = ls;
        return;
    }

    try_to_set_fixed(ci);
}

bool lar_solver::try_to_set_fixed(column_info<mpq> & ci) {
    if (ci.upper_bound_is_set() && ci.low_bound_is_set() && ci.get_upper_bound() == ci.get_low_bound() && !ci.is_fixed()) {
        ci.set_fixed_value(ci.get_upper_bound());
        return true;
    }
    return false;
}

void lar_solver::set_low_bound_for_column_info(constraint_index i, const lar_normalized_constraint & norm_constr) {
    const mpq & v = norm_constr.m_right_side;
    const canonic_left_side & ls = norm_constr.m_canonic_left_side;
    ul_pair ul =  m_map_of_canonic_left_sides[ls];
    column_info_with_cls ci_cls = m_map_from_var_index_to_column_info_with_cls[ul.m_additional_var_index];
    column_info<mpq> &ci = ci_cls.m_column_info;
    lean_assert(norm_constr.m_kind == GE || norm_constr.m_kind == GT || norm_constr.m_kind == EQ);
    bool strict = norm_constr.m_kind == GT;
    if (!ci.low_bound_is_set()) {
        ci.set_low_bound(v);
        ul.m_low_bound_witness = i;
        ci.set_low_bound_strict(strict);
    } else if (ci.get_low_bound() < v) {
        ci.set_low_bound(v);
        ul.m_low_bound_witness = i;
        ci.set_low_bound_strict(strict);
    } else if (ci.get_low_bound() == v && strict && ci.low_bound_is_strict() == false) {
        ul.m_low_bound_witness = i;
        ci.set_low_bound_strict(strict);
    }
    m_map_from_var_index_to_column_info_with_cls[ul.m_additional_var_index] = ci_cls;
    m_map_of_canonic_left_sides[ls] = ul;

    if (ci.is_infeasible()) {
        m_status = INFEASIBLE;
        m_infeasible_canonic_left_side = ls;
        return;
    }

    try_to_set_fixed(ci);
}

void lar_solver::update_column_info_of_normalized_constraint(constraint_index i, const lar_normalized_constraint & norm_constr) {
    lean_assert(norm_constr.size() > 0);
    switch (norm_constr.m_kind) {
    case LE:
    case LT:
        set_upper_bound_for_column_info(i, norm_constr);
        break;
    case GE:
    case GT:
        set_low_bound_for_column_info(i, norm_constr);
        break;
    case EQ:
        set_upper_bound_for_column_info(i, norm_constr);
        set_low_bound_for_column_info(i, norm_constr);
        break;
    default:
        lean_unreachable();
    }
}

column_type lar_solver::get_column_type(const column_info<mpq> & ci) {
    auto ret = ci.get_column_type_no_flipping();
    if (ret == boxed) { // changing boxed to fixed because of the no span
        if (ci.get_low_bound() == ci.get_upper_bound())
            ret = fixed;
    }
    return ret;
}

std::string lar_solver::get_column_name(unsigned j) const 
{
    auto it = m_map_from_var_index_to_column_info_with_cls().find(j);
    if (it == m_map_from_var_index_to_column_info_with_cls().end())
        return std::string("_s") + T_to_string(j);
    return it->second.m_column_info.get_name();
}

void lar_solver::fill_column_types() {
    m_lar_core_solver_params.m_column_types.clear();
    m_lar_core_solver_params.m_column_types.resize(m_map_from_var_index_to_column_info_with_cls.size(), free_column);
    for (auto & it : m_map_from_var_index_to_column_info_with_cls()) {
        const column_info<mpq> & ci = it.second.m_column_info;;
        unsigned j = ci.get_column_index();
        lean_assert(is_valid(j));
        m_lar_core_solver_params.m_column_types[j] = get_column_type(ci);
    }
}

template <typename V>
void lar_solver::fill_bounds_for_core_solver(std::vector<V> & lb, std::vector<V> & ub) {
    unsigned n = A().column_count(); // this is the number of columns
    lb.resize(n);
    ub.resize(n);
    for (auto & t : m_map_from_var_index_to_column_info_with_cls()) {
        const column_info<mpq> & ci = t.second.m_column_info;
        unsigned j = ci.get_column_index();
        lean_assert(j < n);
        if (ci.upper_bound_is_set()) {
            ub[j] = conversion_helper<V>::get_upper_bound(ci);
        }
        if (ci.low_bound_is_set()) {
            lb[j] = conversion_helper<V>::get_low_bound(ci);
        }
    }
}

template <typename V>
void lar_solver::resize_and_init_x_with_zeros(std::vector<V> & x) {
    x.clear();
    x.resize(A().column_count(), zero_of_type<V>()); // init with zeroes, todo - is it necessery?
}

template <typename V>
void lar_solver::resize_and_init_x_with_signature(std::vector<V> & x, std::vector<V> & low_bound,
                                                  std::vector<V> & upper_bound,
                                                  const std::unordered_map<unsigned, non_basic_column_value_position>  & signature) {
    x.resize(low_bound.size());
    for (auto & t : signature) {
        x[t.first] = get_column_val(low_bound, upper_bound, t.second, t.first);
    }
}

template <typename V> V lar_solver::get_column_val(std::vector<V> & low_bound, std::vector<V> & upper_bound, non_basic_column_value_position pos_type, unsigned j) {
    switch (pos_type) {
    case at_low_bound: return low_bound[j];
    case at_fixed:
    case at_upper_bound: return upper_bound[j];
    case free_of_bounds: {
        const auto & it = m_map_from_var_index_to_column_info_with_cls().find(j);
        lean_assert(it != m_map_from_var_index_to_column_info_with_cls().end());
        const auto & ci = it->second.m_column_info;
        if (ci.low_bound_is_set())
            return low_bound[j];
        if (ci.upper_bound_is_set())
            return upper_bound[j];
        return zero_of_type<V>();
    }
    default:
        lean_unreachable();
    }
    return zero_of_type<V>(); // it is unreachable
}

var_index lar_solver::add_var(std::string s) {
    var_index i;
    if (m_var_names_to_var_index.try_get_value(s, i)) {
        return i;
    }
    i = A().column_count();
    A().add_column();
    lean_assert(!m_map_from_var_index_to_column_info_with_cls.contains(i));
    auto ci_with_cls = column_info_with_cls();
    ci_with_cls.m_column_info.set_name(s);
    ci_with_cls.m_column_info.set_column_index(i);
    ci_with_cls.m_canonic_left_side.m_coeffs.emplace_back(1, i); 
    m_map_from_var_index_to_column_info_with_cls[i] = ci_with_cls;
    m_map_of_canonic_left_sides[ci_with_cls.m_canonic_left_side] = ul_pair(i); // we will not create a row in the matrix for this canonic left side
    m_var_names_to_var_index[s] = i;
    return i;
}

bool lar_solver::all_constrained_variables_are_registered(const std::vector<std::pair<mpq, var_index>>& left_side) {
    for (auto it : left_side) {
        var_index vj = it.second;
        if (!m_map_from_var_index_to_column_info_with_cls.contains(vj)) {
            LP_OUT(settings(), "the variable " << vj << " is not registered in its constraint" << std::endl);
            return false;
        }
    }
    return true;
}



constraint_index lar_solver::add_constraint(const std::vector<std::pair<mpq, var_index>>& left_side_with_terms, lconstraint_kind kind_par, mpq right_side_par) {
    std::vector<std::pair<mpq, var_index>> left_side;
    // substitute the terms with their original vars
    for ( auto & t : left_side_with_terms ) {
        if (t.second < m_terms_start_index) {
            left_side.push_back(std::pair<mpq, var_index>(t.first, t.second));
        } else {
            unsigned j = t.second - m_terms_start_index;
            const lar_term & term = m_terms[j];
            for (auto & it : term.m_coeffs) {
                left_side.push_back(std::pair<mpq, var_index>(it.first, it.second));
            }
            right_side_par -= term.m_v;
        }
    }

    
    lean_assert(left_side.size() > 0);
    lean_assert(all_constrained_variables_are_registered(left_side));
    lar_constraint original_constr(left_side, kind_par, right_side_par);
    canonic_left_side ls = create_or_fetch_existing_left_side(left_side);
    mpq ratio = find_ratio_of_original_constraint_to_normalized(ls, original_constr);
    auto kind = ratio.is_neg() ? flip_kind(kind_par) : kind_par;
    mpq right_side = right_side_par / ratio;
    lar_normalized_constraint normalized_constraint(ls, ratio, kind, right_side, original_constr);
    m_normalized_constraints.push_back(normalized_constraint);
    return m_normalized_constraints().size() - 1 ;
}

bool lar_solver::all_constraints_hold() const {
    std::unordered_map<var_index, mpq> var_map;
    get_model(var_map);
    for (auto & it : m_normalized_constraints()) {
        if (!constraint_holds(it.m_origin_constraint, var_map))
            return false;
    }
    return true;
}

bool lar_solver::constraint_holds(const lar_constraint & constr, std::unordered_map<var_index, mpq> & var_map) const {
    mpq left_side_val = get_left_side_val(constr, var_map);
    switch (constr.m_kind) {
    case LE: return left_side_val <= constr.m_right_side;
    case LT: return left_side_val < constr.m_right_side;
    case GE: return left_side_val >= constr.m_right_side;
    case GT: return left_side_val > constr.m_right_side;
    case EQ: return left_side_val == constr.m_right_side;
    default:
        lean_unreachable();
    }
    return false; // it is unreachable
}

void lar_solver::solve_with_core_solver() {
    m_mpq_lar_core_solver.solve();
    m_status = m_mpq_lar_core_solver.m_status;
    lean_assert(m_status != OPTIMAL || all_constraints_hold());
#ifdef LEAN_DEBUG
    lean_assert(!settings().row_feasibility || m_status != INFEASIBLE || the_evidence_is_correct());
#endif
}

bool lar_solver::the_relations_are_of_same_type(const std::vector<std::pair<mpq, unsigned>> & evidence, lconstraint_kind & the_kind_of_sum) {
    unsigned n_of_G = 0, n_of_L = 0;
    bool strict = false;
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        const lar_normalized_constraint & norm_constr = m_normalized_constraints()[con_ind];
        const lar_constraint & constr = norm_constr.m_origin_constraint;
        lconstraint_kind kind = coeff.is_pos() ? constr.m_kind : flip_kind(constr.m_kind);
        if (kind == GT || kind == LT)
            strict = true;
        if (kind == GE || kind == GT) n_of_G++;
        else if (kind == LE || kind == LT) n_of_L++;
    }
    the_kind_of_sum = n_of_G ? GE : (n_of_L ? LE : EQ);
    if (strict)
        the_kind_of_sum = static_cast<lconstraint_kind>((static_cast<int>(the_kind_of_sum) / 2));

    return n_of_G == 0 || n_of_L == 0;
}

void lar_solver::register_in_map(std::unordered_map<var_index, mpq> & coeffs, const lar_constraint & cn, const mpq & a) {
    for (auto & it : cn.m_left_side_map_from_index_to_coefficient) {
        unsigned j = it.first;
        auto p = coeffs.find(j);
        if (p == coeffs.end()) coeffs[j] = it.second * a;
        else p->second += it.second * a;
    }
}
bool lar_solver::the_left_sides_sum_to_zero(const std::vector<std::pair<mpq, unsigned>> & evidence) {
    std::unordered_map<var_index, mpq> coeff_map;
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lean_assert(con_ind < m_normalized_constraints().size());
        const lar_constraint & constr = m_normalized_constraints()[con_ind].m_origin_constraint;
        register_in_map(coeff_map, constr, coeff);
    }
    for (auto & it : coeff_map) {
        if (!numeric_traits<mpq>::is_zero(it.second)) return false;
    }
    return true;
}

bool lar_solver::the_right_sides_do_not_sum_to_zero(const std::vector<std::pair<mpq, unsigned>> & evidence) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lean_assert(con_ind < m_normalized_constraints().size());
        const lar_constraint & constr = m_normalized_constraints()[con_ind].m_origin_constraint;
        ret += constr.m_right_side * coeff;
    }
    return !numeric_traits<mpq>::is_zero(ret);
}

#ifdef LEAN_DEBUG
bool lar_solver::the_evidence_is_correct() {
    std::vector<std::pair<mpq, unsigned>> evidence;
    get_infeasibility_evidence(evidence);
    lconstraint_kind kind;
    lean_assert(the_relations_are_of_same_type(evidence, kind));
    lean_assert(the_left_sides_sum_to_zero(evidence));
    mpq rs = sum_of_right_sides_of_evidence(evidence);
    switch (kind) {
    case LE: lean_assert(rs < zero_of_type<mpq>());
        break;
    case LT: lean_assert(rs <= zero_of_type<mpq>());
        break;
    case GE: lean_assert(rs > zero_of_type<mpq>());
        break;
    case GT: lean_assert(rs >= zero_of_type<mpq>());
        break;
    case EQ: lean_assert(rs != zero_of_type<mpq>());
        break;
    default:
        lean_assert(false);
        return false;
    }
    return true;
}
#endif

void lar_solver::update_column_info_of_normalized_constraints() {
    for (constraint_index i = 0; i < m_normalized_constraints().size(); i++) {
        update_column_info_of_normalized_constraint(i, m_normalized_constraints()[i]);
        if (m_status == INFEASIBLE)
            break;
    }
}

mpq lar_solver::sum_of_right_sides_of_evidence(const std::vector<std::pair<mpq, unsigned>> & evidence) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lean_assert(con_ind < m_normalized_constraints().size());
        const lar_constraint & constr = m_normalized_constraints()[con_ind].m_origin_constraint;
        ret += constr.m_right_side * coeff;
    }
    return ret;
}

/*
// do not touch additional vars here
void lar_solver::map_var_indices_to_columns_of_A() {
    lean_assert(m_map_from_column_indices_to_var_index.size() == 0);
    int i = 0;
    for (auto & it : m_map_from_var_index_to_column_info_with_cls()) {
        if (it.second.m_canonic_left_side.size() > 0) continue; // skipping the additional varialbe for the left side
        lean_assert(!m_map_from_column_indices_to_var_index.contains(i));
        m_map_from_column_indices_to_var_index[i] = it.first;
        i++;
    }
    // update the column_infos
    for (auto & it : m_map_from_column_indices_to_var_index() ) {
        var_index vi = it.second;
        column_info_with_cls ci_cls = m_map_from_var_index_to_column_info_with_cls[vi];
        ci_cls.m_column_info.set_column_index(it.first);
        m_map_from_var_index_to_column_info_with_cls[vi] = ci_cls;
    }
}
*/

void lar_solver::prepare_independently_of_numeric_type() {
    update_column_info_of_normalized_constraints();
    if (m_status == INFEASIBLE)
        return;
    fill_column_types();
}

template <typename U, typename V>
void lar_solver::prepare_core_solver_fields(static_matrix<U, V> & A, std::vector<V> & x,
    std::vector<V> & low_bound,
    std::vector<V> & upper_bound) {
    create_matrix_A(A);
    fill_bounds_for_core_solver(low_bound, upper_bound);
    if (m_status == INFEASIBLE) {
        lean_assert(m_infeasible_canonic_left_side().size() > 0);
    }
    else {
        resize_and_init_x_with_zeros(x);
        fill_basis_from_canonic_left_sides();
        lean_assert(m_lar_core_solver_params.m_basis.size() == A.row_count());
    }
}
template <typename U, typename V>
void lar_solver::prepare_core_solver_fields_with_signature(static_matrix<U, V> & A, std::vector<V> & x,
                                                           std::vector<V> & low_bound,
                                                           std::vector<V> & upper_bound, const lar_solution_signature & signature) {
    create_matrix_A(A);
    fill_bounds_for_core_solver(low_bound, upper_bound);
    if (m_status == INFEASIBLE) {
        lean_assert(false); // not implemented
    }

    resize_and_init_x_with_signature(x, low_bound, upper_bound, signature);
    lean_assert(A.column_count() == x.size());
}

void lar_solver::find_solution_signature_with_doubles(lar_solution_signature & signature) {
    static_matrix<double, double> A;
    std::vector<double> x, low_bounds, upper_bounds;
    prepare_core_solver_fields<double, double>(A, x, low_bounds, upper_bounds);
    std::vector<double> column_scale_vector;
    std::vector<double> right_side_vector(A.row_count(), 0);

    scaler<double, double > scaler(right_side_vector,
        A,
        m_lar_core_solver_params.m_settings.scaling_minimum,
        m_lar_core_solver_params.m_settings.scaling_maximum,
        column_scale_vector,
        m_lar_core_solver_params.m_settings);
    if (!scaler.scale()) {
        // the scale did not succeed, unscaling
        A.clear();
        create_matrix_A(A);
        for (auto & s : column_scale_vector)
            s = 1.0;
    }
    std::vector<double> costs(A.column_count());
    auto core_solver = lp_primal_core_solver<double, double>(A,
                                                             right_side_vector,
                                                             x,
                                                             m_lar_core_solver_params.m_basis,
                                                             costs,
                                                             m_lar_core_solver_params.m_column_types,
                                                             low_bounds,
                                                             upper_bounds,
                                                             m_lar_core_solver_params.m_settings,
                                                             *this);
    core_solver.find_feasible_solution();
    extract_signature_from_lp_core_solver(core_solver, signature);
}

template <typename U, typename V>
void lar_solver::extract_signature_from_lp_core_solver(lp_primal_core_solver<U, V> & core_solver, lar_solution_signature & signature) {
    for (auto j : core_solver.m_non_basic_columns)
        signature[j] = core_solver.get_non_basic_column_value_position(j);
}

void lar_solver::solve_on_signature(const lar_solution_signature & signature) {
    prepare_core_solver_fields_with_signature(m_lar_core_solver_params.m_A, m_lar_core_solver_params.m_x, m_lar_core_solver_params.m_low_bounds, m_lar_core_solver_params.m_upper_bounds, signature);
    solve_with_core_solver();
}

lp_status lar_solver::solve() {
    prepare_independently_of_numeric_type();
    if (m_status == INFEASIBLE)
        return m_status;
    if (need_to_presolve_with_double_solver()) {
        lar_solution_signature solution_signature;
        find_solution_signature_with_doubles(solution_signature);
        // here the basis that is kept in m_basis is the same that was used in the double solver
        solve_on_signature(solution_signature);
        return m_status;
    }
    prepare_core_solver_fields(m_lar_core_solver_params.m_A, m_lar_core_solver_params.m_x, m_lar_core_solver_params.m_low_bounds, m_lar_core_solver_params.m_upper_bounds);
    solve_with_core_solver();
    return m_status;
}

void lar_solver::fill_evidence_from_canonic_left_side(std::vector<std::pair<mpq, constraint_index>> & evidence) {
    // this is the case when the lower bound is in conflict with the upper one
    const ul_pair & ul =  m_map_of_canonic_left_sides[m_infeasible_canonic_left_side];
    const lar_normalized_constraint & bound_constr_u = m_normalized_constraints()[ul.m_upper_bound_witness];
    evidence.push_back(std::make_pair(numeric_traits<mpq>::one() / bound_constr_u.m_ratio_to_original, ul.m_upper_bound_witness));
    const lar_normalized_constraint & bound_constr_l = m_normalized_constraints()[ul.m_low_bound_witness];
    evidence.push_back(std::make_pair(-numeric_traits<mpq>::one() / bound_constr_l.m_ratio_to_original, ul.m_low_bound_witness));
}

void lar_solver::get_infeasibility_evidence(std::vector<std::pair<mpq, constraint_index>> & evidence) {
    if (m_infeasible_canonic_left_side().size() > 0) {
        fill_evidence_from_canonic_left_side(evidence);
        return;
    }
    if (m_mpq_lar_core_solver.get_infeasible_row_sign() == 0) {
        return;
    }
    // the infeasibility sign
    int inf_sign;
    auto inf_row = m_mpq_lar_core_solver.get_infeasibility_info(inf_sign);
    lean_assert(inf_sign != 0);
    get_infeasibility_evidence_for_inf_sign(evidence, inf_row, inf_sign);
}

void lar_solver::get_infeasibility_evidence_for_inf_sign(std::vector<std::pair<mpq, constraint_index>> & evidence,
    const std::vector<std::pair<mpq, unsigned>> & inf_row,
    int inf_sign) {
    for (auto & it : inf_row) {
        mpq coeff = it.first;
        unsigned j = it.second;
        const column_info_with_cls & ci_cls =  m_map_from_var_index_to_column_info_with_cls[j];
        const canonic_left_side & ls = ci_cls.m_canonic_left_side;
        int adj_sign = coeff.is_pos() ? inf_sign : -inf_sign;
        const ul_pair & ul = m_map_of_canonic_left_sides[ls];

        constraint_index bound_constr_i = adj_sign < 0 ? ul.m_upper_bound_witness : ul.m_low_bound_witness;
        lean_assert(bound_constr_i < m_normalized_constraints().size());
        const lar_normalized_constraint & bound_constr = m_normalized_constraints()[bound_constr_i];
        evidence.push_back(std::make_pair(coeff / bound_constr.m_ratio_to_original, bound_constr_i));
    }
}


mpq lar_solver::find_delta_for_strict_bounds() const{
    mpq delta = numeric_traits<mpq>::one();
    for (auto & t : m_map_of_canonic_left_sides()) {
        const column_info<mpq> & ci = get_column_info_from_var_index(t.second.m_additional_var_index);
        unsigned j = ci.get_column_index();
        lean_assert(is_valid(j));
        if (ci.low_bound_is_set())
            restrict_delta_on_low_bound_column(delta, j);
        if (ci.upper_bound_is_set())
            restrict_delta_on_upper_bound(delta, j);
    }
    return delta;
}

void lar_solver::restrict_delta_on_low_bound_column(mpq& delta, unsigned j) const {
    lean_assert(delta > numeric_traits<mpq>::zero());
    const numeric_pair<mpq> & x = m_lar_core_solver_params.m_x[j];
    const numeric_pair<mpq> & l = m_lar_core_solver_params.m_low_bounds[j];
    const mpq & xx = x.x;
    const mpq & xy = x.y;
    if (!xy.is_neg()) return;
    const mpq & lx = l.x;
    lean_assert(xx > lx);
    // we need lx <= xx + delta*xy, or delta*xy >= lx - xx, or - delta*xy <= xx - ls.
    // The right part is not negative. The delta is positive. If xy >= 0 we have the ineqality
    // otherwise we need to have delta not greater than - (xx - lx)/xy. We use the 2 coefficient to handle the strict case
    if (xy >= zero_of_type<mpq>()) return;
    delta = std::min(delta, (lx - xx) / (2 * xy)); // we need to have delta * xy < xx - lx for the strict case
}
void lar_solver::restrict_delta_on_upper_bound(mpq& delta, unsigned j) const {
    const numeric_pair<mpq> & x = m_lar_core_solver_params.m_x[j];
    const numeric_pair<mpq> & u = m_lar_core_solver_params.m_upper_bounds[j];
    const mpq & xx = x.x;
    const mpq & xy = x.y;
    const mpq & ux = u.x;
    if (!xy.is_pos()) return;
    if (xx >= ux) {
        std::cout << "name = " << get_variable_name(j) << std::endl;
        std::cout << "x = " << T_to_string(x) << ", u = " << T_to_string(u) << std::endl;
        std::cout << "x = (" << T_to_string(xx.get_double()) <<","
                  << T_to_string(xy.get_double()) << "), u = (" <<
            T_to_string(ux.get_double()) << "," << T_to_string(u.y.get_double()) << ")" << std::endl;
    }
    lean_assert(xx < ux);
    delta = std::min(delta, (ux - xx) / (2 * xy)); // we need to have delta * xy < ux - xx, for the strict case
}
void lar_solver::get_model(std::unordered_map<var_index, mpq> & variable_values) const {
    lean_assert(m_status == OPTIMAL);
    mpq delta = find_delta_for_strict_bounds();
    for (auto & it : m_map_from_var_index_to_column_info_with_cls()) {
        const column_info<mpq> & ci = it.second.m_column_info;
        unsigned j = ci.get_column_index();
        const numeric_pair<mpq> & rp = m_lar_core_solver_params.m_x[j];
        variable_values[it.first] = rp.x + delta * rp.y;
    }
}

std::string lar_solver::get_variable_name(var_index vi) const {
    return get_column_name(vi);
}

// ********** print region start
void lar_solver::print_constraint(constraint_index ci, std::ostream & out) {
    if (ci >= m_normalized_constraints().size()) {
        out << "constraint " << T_to_string(ci) << " is not found";
        out << std::endl;
        return;
    }

    print_constraint(&m_normalized_constraints()[ci], out);
}

void lar_solver::print_constraints(std::ostream& out) {
    for (auto & it : m_normalized_constraints()) {
        print_constraint(& it, out);
    }
}

void lar_solver::print_canonic_left_side(const canonic_left_side & c, std::ostream & out) {
    m_mpq_lar_core_solver.print_linear_combination_of_column_indices(c.m_coeffs, out);
}

void lar_solver::print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out) {
    m_mpq_lar_core_solver.print_linear_combination_of_column_indices(c->get_left_side_coefficients(), out);
}

// void lar_solver::print_info_on_column(unsigned j, std::ostream & out) {
//     for (auto ls : m_map_of_canonic_left_sides) {
//         if (static_cast<unsigned>(ls->get_ci()) == j) {
//             auto & ci = ls->m_column_info;
//             if (ci.low_bound_is_set()) {
//                 out << "l = " << ci.get_low_bound();
//             }
//             if (ci.upper_bound_is_set()) {
//                 out << "u = " << ci.get_upper_bound();
//             }
//             out << std::endl;
//             m_mpq_lar_core_solver.print_column_info(j, out);
//         }
//     }
// }

mpq lar_solver::get_infeasibility_of_solution(std::unordered_map<std::string, mpq> & solution) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : m_normalized_constraints()) {
        ret += get_infeasibility_of_constraint(it, solution);
    }
    return ret;
}

mpq lar_solver::get_infeasibility_of_constraint(const lar_normalized_constraint & norm_constr, std::unordered_map<std::string, mpq> & solution) {
    auto kind = norm_constr.m_kind;
    mpq left_side_val = get_canonic_left_side_val(norm_constr.m_canonic_left_side, solution);

    switch (kind) {
    case LT:
    case LE: return std::max(left_side_val - norm_constr.m_right_side, numeric_traits<mpq>::zero());
    case GT:
    case GE: return std::max(-(left_side_val - norm_constr.m_right_side), numeric_traits<mpq>::zero());

    case EQ:
        return abs(left_side_val - norm_constr.m_right_side);

    default:
        lean_unreachable();
    }
    return mpq(0); // it is unreachable
}

mpq lar_solver::get_canonic_left_side_val(const canonic_left_side & ls, std::unordered_map<std::string, mpq> & solution) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : ls.m_coeffs) {
        var_index vi = it.second;
        std::string s = get_variable_name(vi);
        auto t = solution.find(s);
        lean_assert(t != solution.end());
        ret += it.first * (t->second);
    }
    return ret;
}

mpq lar_solver::get_left_side_val(const lar_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : cns.m_left_side_map_from_index_to_coefficient) {
        var_index j = it.first;
        auto vi = var_map.find(j);
        lean_assert(vi != var_map.end());
        ret += it.second * vi->second;
    }
    return ret;
}

void lar_solver::print_constraint(const lar_base_constraint * c, std::ostream & out) {
    print_left_side_of_constraint(c, out);
    out << " " << lconstraint_kind_string(c->m_kind) << " " << c->m_right_side << std::endl;
}

void lar_solver::fill_var_set_for_random_update(unsigned sz, var_index const * vars, std::vector<unsigned>& column_list) {
    for (unsigned i = 0; i < sz; i++) {
        var_index var = vars[i];
        lean_assert(m_map_from_var_index_to_column_info_with_cls.contains(var));
        const column_info_with_cls& ci_cls = m_map_from_var_index_to_column_info_with_cls[var];
        unsigned var_column_index = ci_cls.m_column_info.get_column_index();
        column_list.push_back(var_column_index);
    }
}

void lar_solver::random_update(unsigned sz, var_index const * vars) {
    std::vector<unsigned> column_list;
    fill_var_set_for_random_update(sz, vars, column_list);
    random_updater ru(m_mpq_lar_core_solver, column_list);
    ru.update();
}



const column_info<mpq> & lar_solver::get_column_info_from_var_index(var_index vi) const {
    if (! m_map_from_var_index_to_column_info_with_cls.contains(vi)) {
        lean_assert(false);
        throw 0;
    }
    const column_info_with_cls & c = m_map_from_var_index_to_column_info_with_cls[vi];
    return c.m_column_info;
}
void lar_solver::try_pivot_fixed_vars_from_basis() {
    m_mpq_lar_core_solver.pivot_fixed_vars_from_basis();
}

void lar_solver::push() {
    m_status.push();
    m_map_of_canonic_left_sides.push();
    m_normalized_constraints.push();
    m_map_from_var_index_to_column_info_with_cls.push();
    m_lar_core_solver_params.push();
    m_var_names_to_var_index.push();
    m_infeasible_canonic_left_side.push();
    m_terms.push();
}

void lar_solver::pop() {
    pop(1);
}

void lar_solver::pop(unsigned k) {
    m_status.pop(k);
    m_map_of_canonic_left_sides.pop(k);
    m_normalized_constraints.pop(k);
    m_map_from_var_index_to_column_info_with_cls.pop(k);
    m_lar_core_solver_params.pop(k);
    m_var_names_to_var_index.pop(k);
    m_infeasible_canonic_left_side.pop(k);
    m_terms.pop(k);
    if (m_mpq_lar_core_solver.m_factorization != nullptr) {
        delete m_mpq_lar_core_solver.m_factorization;
        m_mpq_lar_core_solver.m_factorization = nullptr;
    }
    m_mpq_lar_core_solver.zero_pivot_row();

}
}

