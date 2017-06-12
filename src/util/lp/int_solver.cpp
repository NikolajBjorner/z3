/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
namespace lean {

bool int_solver::check() {
	if (m_solver->model_is_int_feasible())
		return true;
	return false;
}

int_solver::int_solver(lar_solver* lar_slv) : m_solver(lar_slv) {}
}
