/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "lp_params.hpp"
#include "util/lp/lp_settings.h"
#include "util/lp/mps_reader.h"



void run_solver(lp_params & parms, char const * mps_file_name) {
    std::string fn(mps_file_name);
    lean::mps_reader<double, double> reader(fn);
    reader.set_message_stream(&std::cout); // can be redirected
    reader.read();
    if (!reader.is_ok()) {
        std::cerr << "cannot process " << mps_file_name << std::endl;
        return;
    }
    lean::lp_solver<double, double> * solver =  reader.create_solver(false);  // false - to create the primal solver
    if (parms.min())
        solver->flip_costs();
    solver->settings().set_message_ostream(&std::cout);
    solver->settings().report_frequency = parms.rep_freq();
    solver->settings().print_statistics = parms.print_stats();
    solver->find_maximal_solution();

    *(solver->settings().get_message_ostream()) << "status is " << lp_status_to_string(solver->get_status()) << std::endl;
    if (solver->get_status() != lean::OPTIMAL) {
        return;
    }
    if (parms.min()) {
        solver->flip_costs();
    }
    solver->print_model(std::cout);
    delete solver;
}

unsigned read_mps_file(char const * mps_file_name) {
    lp_params p;
    param_descrs r;
    p.collect_param_descrs(r);
    run_solver(p, mps_file_name);
    return 0;
}
