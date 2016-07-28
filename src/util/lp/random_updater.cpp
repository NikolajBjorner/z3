/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/random_updater.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lar_solver.h"
#include <vector>
namespace lean {


void random_updater::fill_set_of_values_and_set_of_vars(std::vector<unsigned> & column_indices) {
    for (unsigned j : column_indices)
        add_column_to_sets(j);
}

random_updater::random_updater(lar_core_solver<mpq, numeric_pair<mpq>> & lar_core_solver,  std::vector<unsigned> & column_indices) : m_core_solver(lar_core_solver), m_column_j(m_core_solver.m_m())  {
    fill_set_of_values_and_set_of_vars(column_indices);
}

random_updater::interval random_updater::get_interval_of_non_basic_var(unsigned j) {
    interval ret;
    switch (m_core_solver.get_column_type(j)) {
    case free_column:
        break;
    case low_bound:
        ret.set_low_bound(m_core_solver.m_low_bound_values[j]);
        break;
    case upper_bound:
        ret.set_upper_bound(m_core_solver.m_upper_bound_values[j]);
        break;
    case boxed:
    case fixed:
        ret.set_low_bound(m_core_solver.m_low_bound_values[j]);
        ret.set_upper_bound(m_core_solver.m_upper_bound_values[j]);
        break;
    default:
        lean_assert(false);
    }
    return ret;
}

void random_updater::diminish_interval_for_basic_var(numeric_pair<mpq>& nb_x, unsigned j,
                                                     mpq & a,
                                                     interval & r) {
    lean_assert(m_core_solver.m_basis_heading[j] >= 0);
    numeric_pair<mpq> delta;
    lean_assert(a != zero_of_type<mpq>());
    switch (m_core_solver.get_column_type(j)) {
    case free_column:
        break;
    case low_bound:
        delta = m_core_solver.m_x[j] - m_core_solver.m_low_bound_values[j];
        lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
        if (a > 0) {
            r.set_upper_bound(nb_x + delta / a);
        } else {
            r.set_low_bound(nb_x + delta / a);
        }
        break;
    case upper_bound:
        delta = m_core_solver.m_upper_bound_values[j] - m_core_solver.m_x[j];
        lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
        if (a > 0) {
            r.set_low_bound(nb_x - delta / a);
        } else {
            r.set_upper_bound(nb_x - delta / a);
        }
        break;
    case boxed:
        if (a > 0) {
            delta = m_core_solver.m_x[j] - m_core_solver.m_low_bound_values[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_upper_bound(nb_x + delta / a);
            delta = m_core_solver.m_upper_bound_values[j] -m_core_solver.m_x[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_low_bound(nb_x - delta / a);
        } else { // a < 0
            delta = m_core_solver.m_upper_bound_values[j] -m_core_solver.m_x[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_upper_bound(nb_x - delta / a);
            delta = m_core_solver.m_x[j] - m_core_solver.m_low_bound_values[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_low_bound(nb_x + delta / a);
        }
        break;
    case fixed:
          r.set_low_bound(nb_x);
          r.set_upper_bound(nb_x);
          break;
    default:
        lean_assert(false);
    }
}


void random_updater::diminish_interval_to_leave_basic_vars_feasible(numeric_pair<mpq> &nb_x, interval & r) {
    for (unsigned i : m_column_j.m_index) {
        diminish_interval_for_basic_var(nb_x, m_core_solver.m_basis[i], m_column_j.m_data[i], r);
        if (r.is_empty())
            break;
    }
}

random_updater::interval random_updater::find_shift_interval(unsigned j) {
    interval ret = get_interval_of_non_basic_var(j);
    diminish_interval_to_leave_basic_vars_feasible(m_core_solver.m_x[j], ret);
    return ret;
}

void random_updater::shift_var(unsigned j, interval & r) {
    lean_assert(r.contains(m_core_solver.m_x[j]));
    lean_assert(m_core_solver.column_is_feasible(j));
    auto old_x = m_core_solver.m_x[j];
    remove_value(old_x);
    auto new_val = m_core_solver.m_x[j] = get_random_from_interval(r);
    add_value(new_val);

    lean_assert(r.contains(m_core_solver.m_x[j]));
    lean_assert(m_core_solver.column_is_feasible(j));
    auto delta = m_core_solver.m_x[j] - old_x;

    for (unsigned i : m_column_j.m_index) {
        unsigned bj = m_core_solver.m_basis[i];
        m_core_solver.m_x[bj] -= m_column_j[i] * delta;
        lean_assert(m_core_solver.column_is_feasible(bj));
    }
    lean_assert(m_core_solver.A_mult_x_is_off() == false);
}

numeric_pair<mpq> random_updater::get_random_from_interval(interval & r) {
    unsigned rand = my_random();
    if ((!r.low_bound_is_set)  && (!r.upper_bound_is_set))
        return numeric_pair<mpq>(rand % range, 0);
    if (r.low_bound_is_set  && (!r.upper_bound_is_set))
        return r.low_bound + numeric_pair<mpq>(rand % range, 0);
    if ((!r.low_bound_is_set) && r.upper_bound_is_set)
        return r.upper_bound - numeric_pair<mpq>(rand % range, 0);
    lean_assert(r.low_bound_is_set && r.upper_bound_is_set);
    return r.low_bound + (rand % range) * (r.upper_bound - r.low_bound)/ range;
}

void random_updater::random_shift_var(unsigned j) {
    m_core_solver.solve_Bd(j, m_column_j);
    interval interv = find_shift_interval(j);
    if (interv.is_empty()) {
        return;
    }
    shift_var(j, interv);
}

void random_updater::update() {
    std::cout << "we have " << m_var_set.size() << " variables, and " << m_values.size() << " different values" << std::endl;
    for (auto j : m_var_set) {
        if (m_var_set.size() <= m_values.size()) {
            break; // we are done
        }
        random_shift_var(j);
    }
    std::cout << "after run : we have " << m_var_set.size() << " variables, and " << m_values.size() << " different values" << std::endl;
}

void random_updater::add_value(numeric_pair<mpq>& v) {
    auto it = m_values.find(v);
    if (it == m_values.end()) {
        m_values[v] = 1;
    } else {
        it->second++;
    }
}

void random_updater::remove_value(numeric_pair<mpq>& v) {
    auto it = m_values.find(v);
    lean_assert(it != m_values.end());
    it->second--;
    if (it->second == 0)
        m_values.erase(it);
}


void random_updater::add_column_to_sets(unsigned j) {
    if (m_core_solver.m_basis_heading[j] < 0) {
        m_var_set.insert(j);
        add_value(m_core_solver.m_x[j]);
    } else {
        unsigned row = m_core_solver.m_basis_heading[j];
        for (auto row_c : m_core_solver.m_A.m_rows[row]) {
            unsigned cj = row_c.m_j;
            if (m_core_solver.m_basis_heading[cj] < 0) {
                m_var_set.insert(cj);
                add_value(m_core_solver.m_x[cj]);
            }
        }
    }
}
}
