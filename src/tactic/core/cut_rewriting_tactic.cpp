/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    cut_rewriting_tactic.cpp

Abstract:

    Cut rewriting tactic

Author:

    Nikolaj Bjorner (nbjorner) 2019-11-17

Notes:
 
- find size of cut subexpressions see if they can be recompiled to "known" functions.
- get information of cut size distribution for clashes


--*/
#include "ast/expr_network.h"
#include "ast/ast_ll_pp.h"
#include "tactic/tactical.h"
#include "tactic/core/cut_rewriting_tactic.h"

class cut_rewriting_tactic : public tactic {
    ast_manager& m;
    
    bool rewrite(goal & g, unsigned max_cut_size, unsigned max_cutset_size) {
        SASSERT(g.is_well_sorted());
        bool proofs_enabled = g.proofs_enabled();
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        unsigned size = g.size();
        expr_network nw(m);

        for (unsigned idx = 0; idx < size; idx++) {
            nw.add_root(g.form(idx));
        }
        vector<expr_network::cut_set> cuts = nw.get_cuts(max_cut_size, max_cutset_size);
        map<expr_network::cut const*, unsigned, expr_network::cut::hash_proc, expr_network::cut::eq_proc> cut2id;
        unsigned num_cuts = 0, num_clash = 0;
        unsigned_vector cut_sizes;
        for (unsigned i = cuts.size(); i-- > 0; ) {
            num_cuts += cuts[i].size();
            for (auto const& cut : cuts[i]) {
                unsigned j = 0;
                if (cut2id.find(&cut, j)) {
                    VERIFY(i != j);
                    ++num_clash;
                    if (cut.m_size == 1) {
                        //std::cout << mk_bounded_pp(nw.nodes()[i].e(), m, 3) << "\n";
                        //std::cout << mk_bounded_pp(nw.nodes()[j].e(), m, 3) << "\n";
                    }
                    if (nw.depth(i) < nw.depth(j)) {
                        nw.substitute(j, i);
                        cut2id.insert(&cut, i);
                    }
                    else {
                        nw.substitute(i, j);
                    }
                    cut_sizes.reserve(cut.m_size+1, 0);
                    cut_sizes[cut.m_size]++;
                    break;
                }
                else {
                    cut2id.insert(&cut, i);
                }
            }
        }
        IF_VERBOSE(1, verbose_stream() << "(tactic.cut-rewriting :num-cuts " << num_cuts << " :num-clash " << num_clash;
                   if (!cut_sizes.empty()) {
                       verbose_stream() << " :cuts";
                       for (unsigned cs : cut_sizes) verbose_stream() << " " << cs;                       
                   }
                   verbose_stream() << ")\n";);                
        expr_ref_vector new_goals = nw.get_roots();
        for (unsigned idx = 0; idx < size; idx++) {
            if (g.form(idx) != new_goals.get(idx)) {
                if (proofs_enabled) {
                    // TBD: add rewrite proof step
                }
                g.update(idx, new_goals.get(idx), new_pr, g.dep(idx));
            }
        }

        return cuts.size() <= 100 * num_clash;
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
        goal& g = *in.get();
        tactic_report report("cut-rewriting", g);
        TRACE("before_cut", g.display(tout););
        unsigned max_cutset_size = 8;
        unsigned max_cut_size = 4;
        while (rewrite(g, max_cut_size, max_cutset_size)) {
            max_cutset_size = (max_cutset_size*3)/2;
            max_cut_size = std::min(max_cut_size+1, expr_network::cut::max_cut_size);
            max_cut_size = expr_network::cut::max_cut_size;
        }
        g.elim_redundancies();
        TRACE("after_cut", g.display(tout););
        SASSERT(g.is_well_sorted());
        g.inc_depth();
        result.push_back(in.get());
    }

    void cleanup() override {
    }
    
};

tactic * mk_cut_rewriting_tactic(ast_manager & m) {
    return alloc(cut_rewriting_tactic, m);
}
