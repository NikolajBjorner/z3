/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <set>
#include <string>
#include <vector>
#include "util/lp/lp_utils.h"
#include "util/lp/lp_core_solver_base.h"
namespace lean {
void init_basic_part_of_basis_heading(std::vector<unsigned> & basis, std::vector<int> & basis_heading) {
    unsigned m = basis.size();
    for (unsigned i = 0; i < m; i++) {
        unsigned column = basis[i];
        basis_heading[column] = i;
    }
}

void init_non_basic_part_of_basis_heading(std::vector<int> & basis_heading, std::vector<unsigned> & non_basic_columns) {
    non_basic_columns.clear();
    for (int j = basis_heading.size(); j--;){
        if (basis_heading[j] < 0) {
            non_basic_columns.push_back(j);
            // the index of column j in m_non_basic_columns is (- basis_heading[j] - 1)
            basis_heading[j] = - static_cast<int>(non_basic_columns.size());
        }
    }
}
void init_basis_heading_and_non_basic_columns_vector(std::vector<unsigned> & basis,
                                                     std::vector<int> & basis_heading,
                                                     std::vector<unsigned> & non_basic_columns) {
    init_basic_part_of_basis_heading(basis, basis_heading);
    init_non_basic_part_of_basis_heading(basis_heading, non_basic_columns);
}

template <typename T, typename X> lp_core_solver_base<T, X>::
lp_core_solver_base(static_matrix<T, X> & A,
                    std::vector<X> & b, // the right side vector
                    std::vector<unsigned> & basis,
                    std::vector<X> & x,
                    std::vector<T> & costs,
                    lp_settings & settings,
                    const std::unordered_map<unsigned, std::string> & column_names,
                    std::vector<column_type> & column_types,
                    std::vector<X> & low_bound_values,
                    std::vector<X> & upper_bound_values):
    m_pivot_row_of_B_1(A.row_count()),
    m_pivot_row(A.column_count(), zero_of_type<T>()),
    m_A(A),
    m_b(b),
    m_basis(basis),
    m_x(x),
    m_costs(costs),
    m_settings(settings),
    m_y(m_m()),
    m_status(FEASIBLE),
    m_factorization(nullptr),
    m_column_names(column_names),
    m_w(m_m()),
    m_d(m_n()),
    m_ed(m_m()),
    m_column_type(column_types),
    m_low_bound_values(low_bound_values),
    m_upper_bound_values(upper_bound_values),
    m_column_norms(m_n(), T(1)),
    m_copy_of_xB(m_m()),
    m_steepest_edge_coefficients(A.column_count()) {
    if (m_m()) {
        init();
        init_basis_heading();
    }
    }

template <typename T, typename X> void lp_core_solver_base<T, X>::
allocate_basis_heading() { // the rest of initilization will be handled by the factorization class
    m_basis_heading.clear();
    m_basis_heading.resize(m_n(), -1);
}
template <typename T, typename X> void lp_core_solver_base<T, X>::
init() {
    lean_assert(m_costs.size() == m_n());
    lean_assert(m_basis.size() == m_m());
    lean_assert(m_b.size() == m_m());
    allocate_basis_heading();
    init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
    unsigned seed = 1;
    my_random_init(&seed);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
fill_cb(T * y){
    for (unsigned i = 0; i < m_m(); i++) {
        y[i] = m_costs[m_basis[i]];
    }
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
fill_cb(std::vector<T> & y){
    for (unsigned i = 0; i < m_m(); i++) {
        y[i] = m_costs[m_basis[i]];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
solve_yB(std::vector<T> & y) {
    fill_cb(y); // now y = cB, that is the projection of costs to basis
    m_factorization->solve_yB(y);
}

// template <typename T, typename X> void lp_core_solver_base<T, X>::
// update_index_of_ed() {
//     m_index_of_ed.clear();
//     unsigned i = static_cast<unsigned>(m_ed.size());
//     while (i--) {
//         if (!is_zero(m_ed[i]))
//             m_index_of_ed.push_back(i);
//     }
// }
template <typename T, typename X> void lp_core_solver_base<T, X>::solve_Bd(unsigned entering, indexed_vector<T> & column) {
    m_factorization->solve_Bd_faster(entering, column);
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
solve_Bd(unsigned entering) {
    m_factorization->solve_Bd(entering, m_ed, m_w);
    lean_assert(m_w.is_OK());
#ifdef LEAN_DEBUG
    // auto B = get_B(m_factorization);
    // vector<T>  a(m_m);
    // m_A.copy_column_to_vector(entering, a);
    // vector<T> cd(m_ed);
    // B.apply_from_left(cd, m_settings);
    // lean_assert(vectors_are_equal(cd , a));
#endif
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
pretty_print(std::ostream & out) {
    core_solver_pretty_printer<T, X> pp(*this, out);
    pp.print();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
save_state(T * w_buffer, T * d_buffer) {
    copy_m_w(w_buffer);
    copy_m_ed(d_buffer);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_state(T * w_buffer, T * d_buffer) {
    restore_m_w(w_buffer);
    restore_m_ed(d_buffer);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_m_w(T * buffer) {
    unsigned i = m_m();
    while (i --) {
        buffer[i] = m_w[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_m_w(T * buffer) {
    m_w.m_index.clear();
    unsigned i = m_m();
    while (i--) {
        if (!is_zero(m_w[i] = buffer[i]))
            m_w.m_index.push_back(i);
    }
}

// needed for debugging
template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_m_ed(T * buffer) {
    unsigned i = m_m();
    while (i --) {
        buffer[i] = m_ed[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_m_ed(T * buffer) {
    unsigned i = m_m();
    while (i --) {
        m_ed[i] = buffer[i];
    }
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
A_mult_x_is_off() {
    lean_assert(m_x.size() == m_A.column_count());
    if (precise<T>()) {
        for (unsigned i = 0; i < m_m(); i++) {
            X delta = m_b[i] - m_A.dot_product_with_row(i, m_x);
            if (delta != numeric_traits<X>::zero()) {
                // std::cout << "x is off (";
                // std::cout << "m_b[" << i  << "] = " << m_b[i] << " ";
                // std::cout << "left side = " << m_A.dot_product_with_row(i, m_x) << ' ';
                // std::cout << "delta = " << delta << ' ';
                // std::cout << "iters = " << total_iterations() << ")" << std::endl;
                return true;
            }
        }
        return false;
    }

    T feps = convert_struct<T, double>::convert(m_settings.refactor_tolerance);
    X one = convert_struct<X, double>::convert(1.0);
    for (unsigned i = 0; i < m_m(); i++) {
        X delta = abs(m_b[i] - m_A.dot_product_with_row(i, m_x));
        X eps = feps * (one + T(0.1) * abs(m_b[i]));

        if (delta > eps) {
#if 0
            LP_OUT(m_settings, "x is off ("
                << "m_b[" << i  << "] = " << m_b[i] << " "
                << "left side = " << m_A.dot_product_with_row(i, m_x) << ' '
                << "delta = " << delta << ' '
                   << "iters = " << total_iterations() << ")" << std::endl);
#endif
            return true;
        }
    }
    return false;
}
// from page 182 of Istvan Maros's book
template <typename T, typename X> void lp_core_solver_base<T, X>::
calculate_pivot_row_of_B_1(unsigned pivot_row) {
    unsigned i = m_m();
    while (i--) {
        m_pivot_row_of_B_1[i] = numeric_traits<T>::zero();
    }
    m_pivot_row_of_B_1[pivot_row] = numeric_traits<T>::one();
    m_factorization->solve_yB(m_pivot_row_of_B_1);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
zero_pivot_row() {
    for (unsigned j : m_pivot_row_index)
        m_pivot_row[j] = numeric_traits<T>::zero();
    m_pivot_row_index.clear();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
calculate_pivot_row_when_pivot_row_of_B1_is_ready() {
    zero_pivot_row();
    int i = m_m();
    while (i--) {
        T pi_1 = m_pivot_row_of_B_1[i];
        if (numeric_traits<T>::is_zero(pi_1)) {
            continue;
        }
        for (auto & c : m_A.m_rows[i]) {
            unsigned j = c.m_j;
            if (m_factorization->m_basis_heading[j] < 0) {
                m_pivot_row[j] += c.get_val() * pi_1;
            }
        }
    }

    unsigned j = static_cast<unsigned>(m_pivot_row.size());
    while (j--) {
        if (!is_zero(m_pivot_row[j]))
            m_pivot_row_index.push_back(j);
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
update_x(unsigned entering, X delta) {
    if (is_zero(delta)) {
        return;
    }
    m_x[entering] += delta;
    for (unsigned i : m_ed.m_index) {
        m_copy_of_xB[i] = m_x[m_basis[i]];
        m_x[m_basis[i]] -= delta * m_ed[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
print_statistics(char const* str, X cost) {
    LP_OUT(m_settings, str << "iterations = " << (total_iterations() - 1) << ", cost = " << T_to_string(cost)
                           << ", nonzeros = " << m_factorization->get_number_of_nonzeroes() << std::endl);
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
print_statistics_with_iterations_and_check_that_the_time_is_over() {
    unsigned total_iterations = inc_total_iterations();
    if (m_settings.print_statistics && (total_iterations % m_settings.report_frequency == 0)) {
        print_statistics("", X());
    }
    return time_is_over();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const* str) {
    unsigned total_iterations = inc_total_iterations();
    if (m_settings.print_statistics && (total_iterations % m_settings.report_frequency == 0)) {
        print_statistics(str, get_cost());
    }
    return time_is_over();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
print_statistics_with_cost_and_check_that_the_time_is_over(X cost) {
    unsigned total_iterations = inc_total_iterations();
    if (m_settings.print_statistics && (total_iterations % m_settings.report_frequency == 0)) {
        print_statistics("", cost);
    }
    return time_is_over();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
set_non_basic_x_to_correct_bounds() {
    for (unsigned j : non_basis()) {
        switch (m_column_type[j]) {
        case boxed:
            m_x[j] = m_d[j] < 0? m_upper_bound_values[j]: m_low_bound_values[j];
            break;
        case low_bound:
            m_x[j] = m_low_bound_values[j];
            lean_assert(column_is_dual_feasible(j));
            break;
        case upper_bound:
            m_x[j] = m_upper_bound_values[j];
            lean_assert(column_is_dual_feasible(j));
            break;
        default:
            break;
        }
    }
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
column_is_dual_feasible(unsigned j) const {
    switch (m_column_type[j]) {
    case fixed:
    case boxed:
        return (x_is_at_low_bound(j) && d_is_not_negative(j)) ||
            (x_is_at_upper_bound(j) && d_is_not_positive(j));
    case low_bound:
        return x_is_at_low_bound(j) && d_is_not_negative(j);
    case upper_bound:
        LP_OUT(m_settings,  "upper_bound type should be switched to low_bound" << std::endl);
        lean_assert(false); // impossible case
    case free_column:
        return numeric_traits<X>::is_zero(m_d[j]);
    default:
        LP_OUT(m_settings,  "column = " << j << std::endl);
        LP_OUT(m_settings,  "unexpected column type = " << column_type_to_string(m_column_type[j]) << std::endl);
        lean_unreachable();
    }
    lean_unreachable();
    return false;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
d_is_not_negative(unsigned j) const {
    if (numeric_traits<T>::precise()) {
        return m_d[j] >= numeric_traits<T>::zero();
    }
    return m_d[j] > -T(0.00001);
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
d_is_not_positive(unsigned j) const {
    if (numeric_traits<T>::precise()) {
        return m_d[j] <= numeric_traits<T>::zero();
    }
    return m_d[j] < T(0.00001);
}


template <typename T, typename X> bool lp_core_solver_base<T, X>::
time_is_over() {
    if (m_settings.get_cancel_flag()) {
        m_status = lp_status::TIME_EXHAUSTED;
        return true;
    }
    else {
        return false;
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
rs_minus_Anx(std::vector<X> & rs) {
    unsigned row = m_m();
    while (row--) {
        auto &rsv = rs[row] = m_b[row];
        for (auto & it : m_A.m_rows[row]) {
            unsigned j = it.m_j;
            if (m_basis_heading[j] < 0) {
                rsv -= m_x[j] * it.get_val();
            }
        }
    }
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
find_x_by_solving() {
    solve_Ax_eq_b();
    bool ret=  !A_mult_x_is_off();
    return ret;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::column_is_feasible(unsigned j) const {
    const X& x = this->m_x[j];
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        if (this->above_bound(x, this->m_upper_bound_values[j])) {
            return false;
        } else if (this->below_bound(x, this->m_low_bound_values[j])) {
            return false;
        } else {
            return true;
        }
        break;
    case low_bound:
        if (this->below_bound(x, this->m_low_bound_values[j])) {
            return false;
        } else {
            return true;
        }
        break;
    case upper_bound:
        if (this->above_bound(x, this->m_upper_bound_values[j])) {
            return false;
        } else {
            return true;
        }
        break;
    case free_column:
        return true;
        break;
    default:
        lean_unreachable();
    }
    return false; // it is unreachable
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::calc_current_x_is_feasible_include_non_basis() const {
    unsigned j = this->m_n();
    while (j--) {
        if (!column_is_feasible(j))
            return false;
    }
    return true;
}


template <typename T, typename X> bool lp_core_solver_base<T, X>::
update_basis_and_x(int entering, int leaving, X const & tt) {
    if (!is_zero(tt)) {
        update_x(entering, tt);
        if (A_mult_x_is_off() && !find_x_by_solving()) {
            init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
            if (!find_x_by_solving()) {
                restore_x(entering, tt);
                lean_assert(!A_mult_x_is_off());
                init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
                m_iters_with_no_cost_growing++;
                if (m_factorization->get_status() != LU_status::OK) {
                    std::stringstream s;
                    s << "failing refactor on off_result for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << total_iterations();
                    throw_exception(s.str());
                }
                return false;
            }
        }
    }

    bool refactor = m_factorization->need_to_refactor();
    if (!refactor) {
        const T &  pivot = this->m_pivot_row[entering]; // m_ed[m_factorization->basis_heading(leaving)] is the same but the one that we are using is more precise
        m_factorization->replace_column(leaving, pivot, m_w);
        if (m_factorization->get_status() == LU_status::OK) {
            m_factorization->change_basis(entering, leaving);
            return true;
        }
    }
    // need to refactor == true
    m_factorization->change_basis(entering, leaving);
    init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
    if (m_factorization->get_status() != LU_status::OK || A_mult_x_is_off()) {
        LP_OUT(m_settings, "failing refactor for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << total_iterations() << std::endl);
        restore_x_and_refactor(entering, leaving, tt);
        lean_assert(!A_mult_x_is_off());
        m_iters_with_no_cost_growing++;
        LP_OUT(m_settings, "rolled back after failing of init_factorization()" << std::endl);
        m_status = UNSTABLE;
        return false;
    }
    return true;
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
init_basis_heading() {
    init_basis_heading_and_non_basic_columns_vector(m_basis, m_basis_heading, m_non_basic_columns);
    lean_assert(basis_heading_is_correct());
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
basis_has_no_doubles() {
    std::set<unsigned> bm;
    for (unsigned i = 0; i < m_m(); i++) {
        bm.insert(m_basis[i]);
    }
    return bm.size() == m_m();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
non_basis_has_no_doubles() {
    std::set<int> bm;
    for (auto j : m_non_basic_columns) {
        bm.insert(j);
    }
    return bm.size() == m_non_basic_columns.size();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
basis_is_correctly_represented_in_heading() {
    for (unsigned i = 0; i < m_m(); i++) {
        if (m_basis_heading[m_basis[i]] != static_cast<int>(i))
            return false;
    }
    return true;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
non_basis_is_correctly_represented_in_heading() {
    for (unsigned i = 0; i < m_non_basic_columns.size(); i++) {
        if (m_basis_heading[m_non_basic_columns[i]] !=  - static_cast<int>(i) - 1)
            return false;
    }
    for (unsigned j = 0; j < m_A.column_count(); j++) {
        if (m_basis_heading[j] >= 0) {
            lean_assert(static_cast<unsigned>(m_basis_heading[j]) < m_A.row_count() && m_basis[m_basis_heading[j]] == j);
        }
    }
    return true;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
basis_heading_is_correct() {
    if (!basis_has_no_doubles()) {
        std::cout << "basis_has_no_doubles" << std::endl;
        return false;
    }

    if (!non_basis_has_no_doubles()) {
        std::cout << "non_basis_has_no_doubles" << std::endl;
        return false;
    }

    if (!basis_is_correctly_represented_in_heading()) {
        std::cout << "basis_is_correctly_represented_in_heading" << std::endl;
        return false;
    }

    if (!non_basis_is_correctly_represented_in_heading()) {
        std::cout << "non_basis_is_correctly_represented_in_heading" << std::endl;
        return false;
    }


    return true;
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_x_and_refactor(int entering, int leaving, X const & t) {
    m_factorization->restore_basis_change(entering, leaving);
    restore_x(entering, t);
    init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
    if (m_factorization->get_status() == LU_status::Degenerated) {
        LP_OUT(m_settings,  "cannot refactor" << std::endl);
        m_status = lp_status::FLOATING_POINT_ERROR;
    }
    //   solve_Ax_eq_b();
    if (A_mult_x_is_off()) {
        LP_OUT(m_settings, "cannot restore solution" << std::endl);
        m_status = lp_status::FLOATING_POINT_ERROR;
        return;
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_x(unsigned entering, X const & t) {
    if (is_zero(t)) return;
    m_x[entering] -= t;
    for (unsigned i : m_ed.m_index) {
        m_x[m_basis[i]]  = m_copy_of_xB[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
fill_reduced_costs_from_m_y_by_rows() {
    unsigned j = m_n();
    while (j--) {
        if (m_factorization->m_basis_heading[j] < 0)
            m_d[j] = m_costs[j];
        else
            m_d[j] = numeric_traits<T>::zero();
    }

    unsigned i = m_m();
    while (i--) {
        const T & y = m_y[i];
        if (is_zero(y)) continue;
        for (row_cell<T> & it : m_A.m_rows[i]) {
            j = it.m_j;
            if (m_factorization->m_basis_heading[j] < 0) {
                m_d[j] -= y * it.get_val();
            }
        }
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_rs_to_xB(std::vector<X> & rs) {
    unsigned j = m_m();
    while (j--) {
        m_x[m_basis[j]] = rs[j];
    }
}

template <typename T, typename X> std::string lp_core_solver_base<T, X>::
column_name(unsigned column) const {
    auto it = m_column_names.find(column);
    if (it == m_column_names.end()) {
        std::string name = T_to_string(column);
        return std::string(std::string("u") + name);
    }
    return it->second;
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_right_side(std::vector<X> & rs) {
    unsigned i = m_m();
    while (i --) {
        rs[i] = m_b[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
add_delta_to_xB(std::vector<X> & del) {
    unsigned i = m_m();
    while (i--) {
        this->m_x[this->m_basis[i]] -= del[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
find_error_in_BxB(std::vector<X>& rs){
    unsigned row = m_m();
    while (row--) {
        auto &rsv = rs[row];
        for (auto & it : m_A.m_rows[row]) {
            unsigned j = it.m_j;
            if (m_basis_heading[j] >= 0) {
                rsv -= m_x[j] * it.get_val();
            }
        }
    }
}

// recalculates the projection of x to B, such that Ax = b, whereab is the right side
template <typename T, typename X> void lp_core_solver_base<T, X>::
solve_Ax_eq_b() {
    std::vector<X> rs(m_m());
    rs_minus_Anx(rs);
    std::vector<X> rrs = rs; // another copy of rs
    m_factorization->solve_By(rs);
    copy_rs_to_xB(rs);
    if (numeric_traits<T>::precise()) return;
    find_error_in_BxB(rrs);
    m_factorization->solve_By(rrs);
    add_delta_to_xB(rrs);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
snap_non_basic_x_to_bound() {
    for (unsigned j : non_basis()) {
        switch (m_column_type[j]) {
        case fixed:
        case boxed:
            if (x_is_at_bound(j))
                break; // we should preserve x if possible
            m_x[j] = m_low_bound_values[j];
            break;
        case low_bound:
            if (x_is_at_low_bound(j))
                break;
            m_x[j] = m_low_bound_values[j];
            break;
        case upper_bound:
            if (x_is_at_upper_bound(j))
                break;
            m_x[j] = m_upper_bound_values[j];
            break;
        default:
            break;
        }
    }
}
template <typename T, typename X> void lp_core_solver_base<T, X>::
snap_non_basic_x_to_bound_and_free_to_zeroes() {
    for (unsigned j : non_basis()) {
        lean_assert(j < m_x.size());
        switch (m_column_type[j]) {
        case fixed:
        case boxed:
        case low_bound:
            m_x[j] = m_low_bound_values[j];
            break;
        case upper_bound:
            m_x[j] = m_upper_bound_values[j];
            break;
        default:
            m_x[j] = zero_of_type<X>();
            break;
        }
    }
}
template <typename T, typename X> void lp_core_solver_base<T, X>::
snap_xN_to_bounds_and_fill_xB() {
    snap_non_basic_x_to_bound();
    solve_Ax_eq_b();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
snap_xN_to_bounds_and_free_columns_to_zeroes() {
    snap_non_basic_x_to_bound_and_free_to_zeroes();
    solve_Ax_eq_b();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
init_reduced_costs_for_one_iteration() {
    solve_yB(m_y);
    fill_reduced_costs_from_m_y_by_rows();
}

template <typename T, typename X> non_basic_column_value_position lp_core_solver_base<T, X>::
get_non_basic_column_value_position(unsigned j) {
    switch (m_column_type[j]) {
    case fixed:
        return at_fixed;
    case free_column:
        return free_of_bounds;
    case boxed:
        return x_is_at_low_bound(j)? at_low_bound : at_upper_bound;
    case low_bound:
        return at_low_bound;
    case upper_bound:
        return at_upper_bound;
    default:
        lean_unreachable();
    }
    lean_unreachable();
    return at_low_bound;
}

template <typename T, typename X> void lp_core_solver_base<T, X>::init_lu() {
    init_factorization(this->m_factorization, this->m_A, this->m_basis, this->m_basis_heading, this->m_settings, this->m_non_basic_columns);
}

template <typename T, typename X> int lp_core_solver_base<T, X>::pivots_in_column_and_row_are_different(int entering, int leaving) const {
    const T & column_p = this->m_ed[this->m_basis_heading[leaving]];
    const T & row_p = this->m_pivot_row[entering];
    if (is_zero(column_p) || is_zero(row_p)) return true; // pivots cannot be zero
    // the pivots have to have the same sign
    if (column_p < 0) {
        if (row_p > 0)
            return 2;
    } else { // column_p > 0
        if (row_p < 0)
            return 2;
    }
    T diff_normalized = abs((column_p - row_p) / (numeric_traits<T>::one() + abs(row_p)));
    if ( !this->m_settings.abs_val_is_smaller_than_harris_tolerance(diff_normalized / T(10)))
        return 1;
    return 0;
}
template <typename T, typename X>  void lp_core_solver_base<T, X>::pivot_fixed_vars_from_basis() {
    // run over basis and non-basis at the same time
    indexed_vector<T> w(m_basis.size()); // the buffer
    unsigned i = 0; // points to basis
    unsigned j = 0; // points to nonbasis
    for (; i < m_basis.size() && j < m_non_basic_columns.size(); i++) {
        unsigned ii = m_basis[i];
        unsigned jj;

        if (get_column_type(ii) != fixed) continue;
        while (j < m_non_basic_columns.size()) {
            for (; j < m_non_basic_columns.size(); j++) {
                jj = m_non_basic_columns[j];
                if (get_column_type(jj) != fixed)
                    break;
            }
            if (j >= m_non_basic_columns.size())
                break;
            j++;
            if (m_factorization->need_to_refactor()) {
                m_factorization->change_basis(jj, ii);
                init_lu();
            } else {
                m_factorization->prepare_entering(jj, w); // to init vector w
                m_factorization->replace_column(ii, zero_of_type<T>(), w);
                m_factorization->change_basis(jj, ii);
            }
            if (m_factorization->get_status() != LU_status::OK) {
                m_factorization->change_basis(ii, jj);
                init_lu();
            } else {
                break;
            }
        }
        lean_assert(m_factorization->get_status()== LU_status::OK)
    }
}
template <typename T, typename X> void lp_core_solver_base<T, X>::
print_linear_combination_of_column_indices(const std::vector<std::pair<T, unsigned>> & coeffs, std::ostream & out) {
    bool first = true;
    for (const auto & it : coeffs) {
        auto val = it.first;
        if (first) {
            first = false;
        } else {
            if (val.is_pos()) {
                out << " + ";
            } else {
                out << " - ";
                val = -val;
            }
        }
        if (val != numeric_traits<mpq>::one())
            out << T_to_string(val);
        out << column_name(it.second);
    }
    std::cout<< std::endl;
}

}
