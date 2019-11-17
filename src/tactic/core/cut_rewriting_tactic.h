/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    cut_rewriting_tactic.h

Abstract:

    Network based rewriting tactic

Author:

    Nikolaj Bjorner 2019-11-17

--*/
#ifndef CUT_REWRITING_TACTIC_H_
#define CUT_REWRITING_TACTIC_H_

class ast_manager;
class tactic;

tactic * mk_cut_rewriting_tactic(ast_manager & m);

/*
  ADD_TACTIC("cut-rewriting", "rewriting based on cut sweep", "mk_cut_rewriting_tactic(m)")
*/

#endif /* CUT_REWRITING_TACTIC_H_ */
