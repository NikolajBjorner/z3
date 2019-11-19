/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    cut_rewriting_tactic.cpp

Abstract:

    Cut rewriting tactic

Author:

    Nikolaj Bjorner (nbjorner) 2019-11-17

--*/
#include "ast/expr_network.h"
#include "tactic/tactical.h"
#include "tactic/core/cut_rewriting_tactic.h"

class cut_rewriting_tactic : public tactic {
    ast_manager& m;

    void rewrite(goal & g) {
        SASSERT(g.is_well_sorted());
        bool proofs_enabled = g.proofs_enabled();
        tactic_report report("cut-rewriting", g);
        TRACE("before_cut", g.display(tout););
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        unsigned size = g.size();
        expr_network nw(m);

        for (unsigned idx = 0; idx < size; idx++) {
            nw.add_root(g.form(idx));
        }
        vector<expr_network::cut_set> cuts = nw.get_cuts(5);
        map<expr_network::cut const*, unsigned, expr_network::cut::hash_proc, expr_network::cut::eq_proc> cut2id;
        unsigned num_cuts = 0, num_clash = 0;
        for (unsigned i = cuts.size(); i-- > 0; ) {
            num_cuts += cuts[i].size();
            for (auto const& cut : cuts[i]) {
                unsigned j = 0;
                if (cut2id.find(&cut, j)) {
                    if (i == j) {
                        std::cout << "cut: " << cut << "\n";
                        for (auto const& c : cuts[i]) {
                            std::cout << c << "\n";
                        }
                        std::cout << "\n";
                        exit(0);
                    }
                    if (i != j) {
                        ++num_clash;
                        std::cout << "clash: " << i << " " << j << "\n";
                        nw.substitute(i, j);
                        break;
                    }
                }
                else {
                    cut2id.insert(&cut, i);
                }
            }
        }
        std::cout << "num cuts: " << num_cuts << " num clash: " << num_clash << "\n";
        
        expr_ref_vector new_goals = nw.get_roots();
        for (unsigned idx = 0; idx < size; idx++) {
            if (g.form(idx) != new_goals.get(idx)) {
                if (proofs_enabled) {
                    // TBD: add rewrite proof step
                }
                std::cout << "rewrite\n";
                g.update(idx, new_goals.get(idx), new_pr, g.dep(idx));
            }
        }
        std::cout << "updated\n";
        g.elim_redundancies();
        TRACE("after_cut", g.display(tout););
        SASSERT(g.is_well_sorted());
    }

public:
    cut_rewriting_tactic(ast_manager & m): m(m) {
    }

    tactic * translate(ast_manager & m) override {
        return alloc(cut_rewriting_tactic, m);
    }

    ~cut_rewriting_tactic() override {
    }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        rewrite(*(in.get()));
        in->inc_depth();
        result.push_back(in.get());
    }

    void cleanup() override {
    }
    
};

tactic * mk_cut_rewriting_tactic(ast_manager & m) {
    return alloc(cut_rewriting_tactic, m);
}
