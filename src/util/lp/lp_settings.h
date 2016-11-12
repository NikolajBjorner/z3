/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <string>
#include <algorithm>
#include <limits>
#include <sys/timeb.h>
#include <iomanip>
#include "util/lp/lp_utils.h"

namespace lean {
typedef unsigned var_index;
typedef unsigned constraint_index;

enum lar_infeasible_row_search_strategy {
    grab_first,
    uniform_random,
    minimal_index,
    min_row_norm,
};

enum lar_infeasible_column_search_strategy {
    grab_first_col,
    uniform_random_col,
    total_min_column_norm,
    min_col_norm,
};

enum column_type  {
    fixed,
    boxed,
    low_bound,
    upper_bound,
    free_column
};

std::string column_type_to_string(column_type t);

enum lp_status {
    UNKNOWN,
    INFEASIBLE,
    TENTATIVE_UNBOUNDED,
    UNBOUNDED,
    TENTATIVE_DUAL_UNBOUNDED,
    DUAL_UNBOUNDED,
    OPTIMAL,
    FEASIBLE,
    FLOATING_POINT_ERROR,
    TIME_EXHAUSTED,
    ITERATIONS_EXHAUSTED,
    EMPTY,
    UNSTABLE
};

// when the ratio of the vector lenth to domain size to is greater than the return value we switch to solve_By_for_T_indexed_only
template <typename X>
unsigned ratio_of_index_size_to_all_size() {
    if (numeric_traits<X>::precise())
        return 10;
    return 120;
}

const char* lp_status_to_string(lp_status status);

inline std::ostream& operator<<(std::ostream& out, lp_status status) {
    return out << lp_status_to_string(status);
}

lp_status lp_status_from_string(std::string status);

enum non_basic_column_value_position { at_low_bound, at_upper_bound, at_fixed, free_of_bounds };

template <typename X> bool is_epsilon_small(const X & v, const double& eps);    // forward definition

int get_millisecond_count();
int get_millisecond_span(int start_time);
void my_random_init(unsigned * seed);
unsigned my_random();


class lp_resource_limit {
public:
    virtual bool get_cancel_flag() = 0;
};

struct stats {
    unsigned m_total_iterations;
    unsigned m_iters_with_no_cost_growing;
    unsigned m_num_factorizations;
    unsigned m_num_of_implied_bounds;
    stats() { reset(); }
    void reset() { memset(this, 0, sizeof(*this)); }
};

struct lp_settings {
private:
    class default_lp_resource_limit : public lp_resource_limit {
        lp_settings& m_settings;
        int m_start_time;
    public:
        default_lp_resource_limit(lp_settings& s): m_settings(s), m_start_time(get_millisecond_count()) {}
        virtual bool get_cancel_flag() {
            int span_in_mills = get_millisecond_span(m_start_time);
            return (span_in_mills / 1000.0  > m_settings.time_limit);
        }
    };

    default_lp_resource_limit m_default_resource_limit;
    lp_resource_limit* m_resource_limit;
    // used for debug output
    std::ostream* m_debug_out = &std::cout;
    // used for messages, for example, the computation progress messages
    std::ostream* m_message_out = &std::cout;

    stats  m_stats;

public:
    // when the absolute value of an element is less than pivot_epsilon
    // in pivoting, we treat it as a zero
    double pivot_epsilon = 0.00000001;
    // see Chatal, page 115
    double positive_price_epsilon = 1e-7;
    // a quatation "if some choice of the entering vairable leads to an eta matrix
    // whose diagonal element in the eta column is less than e2 (entering_diag_epsilon) in magnitude, the this choice is rejected ...
    double entering_diag_epsilon = 1e-8;
    int c_partial_pivoting = 10; // this is the constant c from page 410
    unsigned depth_of_rook_search = 4;
    bool using_partial_pivoting = true;
    // dissertation of Achim Koberstein
    // if Bx - b is different at any component more that refactor_epsilon then we refactor
    double refactor_tolerance = 1e-4;
    double pivot_tolerance = 1e-6;
    double zero_tolerance = 1e-12;
    double drop_tolerance = 1e-14;
    double tolerance_for_artificials = 1e-4;
    double can_be_taken_to_basis_tolerance = 0.00001;

    unsigned percent_of_entering_to_check = 5; // we try to find a profitable column in a percentage of the columns
    bool use_scaling = true;
    double scaling_maximum = 1;
    double scaling_minimum = 0.5;
    double harris_feasibility_tolerance = 1e-7; // page 179 of Istvan Maros
    double ignore_epsilon_of_harris = 10e-5;
    unsigned max_number_of_iterations_with_no_improvements = 2000000;
    unsigned max_total_number_of_iterations = 20000000;
    double time_limit = std::numeric_limits<double>::max(); // the maximum time limit of the total run time in seconds
    // dual section
    double dual_feasibility_tolerance = 1e-7; // // page 71 of the PhD thesis of Achim Koberstein
    double primal_feasibility_tolerance = 1e-7; // page 71 of the PhD thesis of Achim Koberstein
    double relative_primal_feasibility_tolerance = 1e-9; // page 71 of the PhD thesis of Achim Koberstein


    lp_settings() : m_default_resource_limit(*this), m_resource_limit(&m_default_resource_limit) {}

    void set_resource_limit(lp_resource_limit& lim) { m_resource_limit = &lim; }
    bool get_cancel_flag() const { return m_resource_limit->get_cancel_flag(); }

    void set_debug_ostream(std::ostream* out) { m_debug_out = out; }
    void set_message_ostream(std::ostream* out) { m_message_out = out; }
    
    std::ostream* get_debug_ostream() { return m_debug_out; }
    std::ostream* get_message_ostream() { return m_message_out; }
    stats& st() { return m_stats; }
    stats const& st() const { return m_stats; }

    template <typename T> static bool is_eps_small_general(const T & t, const double & eps) {
        return (!numeric_traits<T>::precise())? is_epsilon_small<T>(t, eps) : numeric_traits<T>::is_zero(t);
    }

    template <typename T>
    bool abs_val_is_smaller_than_dual_feasibility_tolerance(T const & t) {
        return is_eps_small_general<T>(t, dual_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_primal_feasibility_tolerance(T const & t) {
        return is_eps_small_general<T>(t, primal_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_can_be_taken_to_basis_tolerance(T const & t) {
        return is_eps_small_general<T>(t, can_be_taken_to_basis_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_drop_tolerance(T const & t) const {
        return is_eps_small_general<T>(t, drop_tolerance);
    }


    template <typename T>
    bool abs_val_is_smaller_than_zero_tolerance(T const & t) {
        return is_eps_small_general<T>(t, zero_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_refactor_tolerance(T const & t) {
        return is_eps_small_general<T>(t, refactor_tolerance);
    }


    template <typename T>
    bool abs_val_is_smaller_than_pivot_tolerance(T const & t) {
        return is_eps_small_general<T>(t, pivot_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_harris_tolerance(T const & t) {
        return is_eps_small_general<T>(t, harris_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_ignore_epslilon_for_harris(T const & t) {
        return is_eps_small_general<T>(t, ignore_epsilon_of_harris);
    }

    template <typename T>
    bool abs_val_is_smaller_than_artificial_tolerance(T const & t) {
        return is_eps_small_general<T>(t, tolerance_for_artificials);
    }
    // the method of lar solver to use
    bool lar_row_feasibility_only = false;  // we are going away from row_feasibility_loop - remove this field (todo)
    bool presolve_with_double_solver_for_lar = true;
    int report_frequency = 1000;
    bool print_statistics = false;
    unsigned column_norms_update_frequency = 12000;
    bool scale_with_ratio = true;
    double density_threshold = 0.7; // need to tune it up, todo
#ifdef LEAN_DEBUG
    static unsigned ddd; // used for debugging    
#endif
    bool tighten_bounds = false;
    lar_infeasible_row_search_strategy infeasible_row_search_strategy = grab_first;
    lar_infeasible_column_search_strategy infeasible_column_search_strategy = min_col_norm;
    bool use_breakpoints_in_feasibility_search = false;

}; // end of lp_settings class


#define LP_OUT(_settings_, _msg_) { if (_settings_.get_debug_ostream()) { *_settings_.get_debug_ostream() << _msg_; } }

template <typename T>
std::string T_to_string(const T & t) {
    std::ostringstream strs;
    strs << t;
    return strs.str();
}

inline std::string T_to_string(const numeric_pair<mpq> & t) {
    std::ostringstream strs;
    double r = (t.x + t.y / mpq(1000)).get_double();
    strs << r;
    return strs.str();
}


inline std::string T_to_string(const mpq & t) {
    std::ostringstream strs;
    strs << t.get_double();
    return strs.str();
}

template <typename T>
bool val_is_smaller_than_eps(T const & t, double const & eps) {
    if (!numeric_traits<T>::precise()) {
        return numeric_traits<T>::get_double(t) < eps;
    }
    return t <= numeric_traits<T>::zero();
}

template <typename T>
bool vectors_are_equal(T * a, std::vector<T>  &b, unsigned n);

template <typename T>
bool vectors_are_equal(const std::vector<T> & a, const buffer<T>  &b);

template <typename T>
bool vectors_are_equal(const std::vector<T> & a, const std::vector<T> &b);

template <typename T>
T abs (T const & v) { return v >= zero_of_type<T>() ? v : -v; }

template <typename X>
X max_abs_in_vector(std::vector<X>& t){
    X r(zero_of_type<X>());
    for (auto & v : t)
        r = std::max(abs(v) , r);
    return r;
}
inline void print_blanks(int n, std::ostream & out) {
    while (n--) {out << ' '; }
}

#if LEAN_DEBUG
bool D();
#endif
}
