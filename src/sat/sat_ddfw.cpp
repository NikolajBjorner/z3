/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

    sat_ddfw.cpp

  Abstract:
   
    DDFW Local search module for clauses

  Author:

    Nikolaj Bjorner 2019-4-23

  Notes:
  
     http://www.ict.griffith.edu.au/~johnt/publications/CP2006raouf.pdf


  Todo:
  - rephase strategy
  - replace heap by probabilistic priority queue
  - experiment with backoff schemes for restarts
  - import phases from CDCL
  - export reward priorities
  --*/

#include "sat/sat_ddfw.h"
#include "sat/sat_solver.h"
#include "sat/sat_params.hpp"

namespace sat {

    ddfw::~ddfw() {
        for (clause* cp : m_clause_db) {
            m_alloc.del_clause(cp);
        }
    }

    lbool ddfw::check() {
        init();
        while (m_limit.inc() && m_min_sz > 0) {
            bool_var v = pick_var();
            if (m_reward[v] > 0 || (m_reward[v] == 0 && m_rand(100) <= m_config.m_use_reward_zero_pct)) {
                flip(v);
                if (m_unsat.size() < m_min_sz) {
                    save_best_values();
                }
                else if (should_reinit_weights()) {
                    invariant();
                    do_reinit_weights(false);
                }
            }
            else {
                shift_weights();
            }
        } 
        if (m_min_sz == 0) {
            return l_true;
        }
        return l_undef;
    }

    void ddfw::log() {
        double sec = m_stopwatch.get_current_seconds();
        double kflips_per_sec = m_flips / (1000.0 * sec);
        IF_VERBOSE(0, verbose_stream() 
                   << " unsat "   << m_min_sz
                   << " kflips/sec " << kflips_per_sec
                   << " vars: "   << m_reward.size() 
                   << " flips: "  << m_flips 
                   << " reinits: " << m_reinit_count
                   << " unsat_vars " << m_unsat_vars.size()
                   << " shifts: " << m_shifts << "\n");

    }

    bool_var ddfw::pick_var() {
        if (m_config.m_use_heap) {
            return m_heap.min_value();
        }
        else {
            double sum = 0;
            for (bool_var v : m_unsat_vars) {
                int r = m_reward[v];
                if (r > 0) {
                    sum += r;
                }
            }
            double lim = ((double) m_rand() / (1.0 + m_rand.max_value())) * sum;
            for (bool_var v : m_unsat_vars) {
                int r = m_reward[v];
                if (r > 0) {
                    lim -= r;
                    if (lim <= 0) {
                        return v;
                    }
                }
            }
            return m_unsat_vars.elem_at(m_rand(m_unsat_vars.size()));
        }
    }

    void ddfw::add(unsigned n, literal const* c) {        
        clause* cls = m_alloc.mk_clause(n, c, false);
        unsigned idx = m_clause_db.size();
        m_clause_db.push_back(cls);
        m_clauses.push_back(clause_info());
        for (literal lit : *cls) {
            m_use_list.reserve(lit.index()+1);
            m_reward.reserve(lit.var()+1, 0);
            m_use_list[lit.index()].push_back(idx);
        }
    }

    void ddfw::add(solver const& s) {
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            add(1, s.m_trail.c_ptr() + i);
        }
        unsigned sz = s.m_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = ~to_literal(l_idx);
            watch_list const & wlist = s.m_watches[l_idx];
            for (watched const& w : wlist) {
                if (!w.is_binary_non_learned_clause())
                    continue;
                literal l2 = w.get_literal();
                if (l1.index() > l2.index()) 
                    continue;
                literal ls[2] = { l1, l2 };
                add(2, ls);
            }
        }
        for (clause* c : s.m_clauses) {
            add(c->size(), c->begin());
        }        
    }

    void ddfw::init() {
        m_values.reserve(m_reward.size());
        m_make_count.reserve(m_reward.size(), 0);
        for (unsigned v = 0; v < m_reward.size(); ++v) {
            m_values[v] = (m_rand() % 2 == 0);
        }
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            clause_info& info = m_clauses[i];
            clause const& c = get_clause(i);
            info.m_num_trues = 0;
            info.m_weight = m_config.m_init_clause_weight;
            info.m_trues = 0;
            for (literal lit : c) {
                if (is_true(lit)) {
                    info.add(lit);
                }
            }
            if (!info.is_true()) {
                if (c.contains(literal(19579, true)) || c.contains(literal(19579, false))) {
                    IF_VERBOSE(0, verbose_stream() << c << "\n");
                }
                m_unsat.insert(i);
            }
        }
        init_rewards();

        m_reinit_count = 0;
        m_reinit_inc = 10000;
        m_reinit_next = m_reinit_inc;
        m_reinit_next_reset = 1;

        m_min_sz = m_unsat.size();
        m_flips = 0; 
        m_shifts = 0;
        m_stopwatch.start();
    }

    void ddfw::flip(bool_var v) {
        ++m_flips;
        literal lit = literal(v, !m_values[v]);
        literal nlit = ~lit;
        SASSERT(is_true(lit));
        for (unsigned cls_idx : m_use_list[lit.index()]) {
            clause_info& ci = m_clauses[cls_idx];
            ci.del(lit);
            unsigned w = ci.m_weight;
            // cls becomes false: flip any variable in clause to receive reward w
            switch (ci.m_num_trues) {
            case 0: {
                m_unsat.insert(cls_idx);
                clause const& c = get_clause(cls_idx);
                if (c.contains(literal(19579, true)) || c.contains(literal(19579, false))) {
                    IF_VERBOSE(0, verbose_stream() << "add " << lit << " " << cls_idx << ": " << c << "\n");
                }
                VERIFY(c.contains(lit));
                for (literal l : c) {
                    inc_reward(l, w);
                    inc_make(l);
                }
                inc_reward(lit, w);
                break;
                }
            case 1:
                dec_reward(to_literal(ci.m_trues), w);
                break;
            default:
                break;
            }
        }
        for (unsigned cls_idx : m_use_list[nlit.index()]) {
            clause_info& ci = m_clauses[cls_idx];             
            unsigned w = ci.m_weight;
            // the clause used to have a single true (pivot) literal, now it has two.
            // Then the previous pivot is no longer penalized for flipping.
            switch (ci.m_num_trues) {
            case 0: {
                m_unsat.remove(cls_idx);   
                clause const& c = get_clause(cls_idx);
                if (c.contains(literal(19579, true)) || c.contains(literal(19579, false))) {
                    IF_VERBOSE(0, verbose_stream() << "del " << nlit << " " << cls_idx << ": " << c << "\n");
                }
                VERIFY(c.contains(nlit));
                for (literal l : c) {
                    dec_reward(l, w);
                    dec_make(l);
                }
                for (literal l : c) {
                    if (m_make_count[l.var()] == 0) VERIFY(!m_unsat_vars.contains(l.var())); 
                }
                dec_reward(nlit, w);
                break;
            }
            case 1:
                inc_reward(to_literal(ci.m_trues), w);
                break;
            default:
                break;
            }
            ci.add(nlit);
        }
        m_values[v] = !m_values[v];
    }

    bool ddfw::should_reinit_weights() {
        return m_flips > m_reinit_next;
    }

    void ddfw::do_reinit_weights(bool force) {
        log();

        if (!force && m_reinit_count % 2 == 0) { 
            //  TBD have other strategies: m_reinit_count < m_reinit_next_reset
            for (auto& ci : m_clauses) {
                ci.m_weight += 1;                
            }
        }
        else {
            for (auto& ci : m_clauses) {
                if (ci.is_true()) {
                    ci.m_weight = m_config.m_init_clause_weight;
                }
                else {
                    ci.m_weight = m_config.m_init_clause_weight + 1;
                }                
            }
            if (!force) {
                m_reinit_next_reset += m_reinit_count;
            }            
        }
        init_rewards();   
        ++m_reinit_count;
        m_reinit_next += m_reinit_count * m_reinit_inc;
    }

    void ddfw::init_rewards() {
        if (m_config.m_use_heap) {
            m_heap.clear();
            m_heap.reserve(m_reward.size());
            for (unsigned v = 0; v < m_reward.size(); ++v) {
                m_reward[v] = 0;
                m_heap.insert(v);
            }
        }
        else {
            // inc_make below.
        }
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto const& ci = m_clauses[i];
            switch (ci.m_num_trues) {
            case 0:
                for (literal lit : get_clause(i)) {
                    inc_reward(lit, ci.m_weight);
                    inc_make(lit);
                }
                break;
            case 1:
                dec_reward(to_literal(ci.m_trues), ci.m_weight);
                break;
            default:
                break;
            }
        }
    }

    void ddfw::save_best_values() {
        m_model.reserve(m_values.size());
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_model[i] = to_lbool(m_values[i]);
        }
        m_min_sz = m_unsat.size();
    }

    /**
       \brief Filter on whether to select a satisfied clause 
       1. with some probability prefer higher weight to lesser weight.
       2. take into account number of trues
       3. select multiple clauses instead of just one per clause in unsat.
     */

    bool ddfw::select_clause(unsigned max_weight, unsigned max_trues, unsigned weight, unsigned num_trues) {
#if 0
        if (weight < max_weight) return false;
        if (weight > max_weight) return true;
        if (max_trues < num_trues) return true;
#endif
        return true;
    }

    unsigned ddfw::select_max_same_sign(unsigned cf_idx) {
        clause const& c = get_clause(cf_idx);
        unsigned sz = c.size();
        unsigned max_weight = 2;
        unsigned max_trues = 0;
        unsigned cl = UINT_MAX; // clause pointer to same sign, max weight satisfied clause.
        unsigned n = 1;
        for (literal lit : c) {
            auto const& cls = m_use_list[lit.index()];
            for (unsigned cn_idx : cls) {
                auto& cn = m_clauses[cn_idx];
                unsigned num_trues = cn.m_num_trues;
                if (num_trues > 0) {
                    unsigned wn = cn.m_weight;
                    if (wn > max_weight && select_clause(max_weight, max_trues, wn, num_trues)) {
                        cl = cn_idx;
                        max_weight = wn;
                        max_trues = num_trues;
                        n = 2;
                    }
                    else if (wn == max_weight && select_clause(max_weight, max_trues, wn, num_trues) && (m_rand() % (n++)) == 0) {
                        cl = cn_idx;
                        max_weight = wn;
                        max_trues = num_trues;
                    }
                }
            }
        }
        return cl;
    }

    void ddfw::inc_reward(literal lit, int inc) {
        int& r = m_reward[lit.var()];
        r += inc;
        if (m_config.m_use_heap) {
            m_heap.decreased(lit.var());
        }
    }
    
    void ddfw::dec_reward(literal lit, int inc) {
        int& r = m_reward[lit.var()];
        r -= inc;
        if (m_config.m_use_heap) {
            m_heap.increased(lit.var());        
        }
    }

    void ddfw::shift_weights() {
        ++m_shifts;
        for (unsigned cf_idx : m_unsat) {
            auto& cf = m_clauses[cf_idx];
            SASSERT(!cf.is_true());
            unsigned cn_idx = select_max_same_sign(cf_idx);
            while (cn_idx == UINT_MAX) {
                unsigned idx = (m_rand() * m_rand()) % m_clauses.size();
                auto & cn = m_clauses[idx];
                if (cn.is_true() && cn.m_weight >= 2) {
                    cn_idx = idx;
                }
            }
            auto & cn = m_clauses[cn_idx];
            SASSERT(cn.is_true());
            unsigned wn = cn.m_weight;
            SASSERT(wn >= 2);
            unsigned inc = (wn > 2) ? 2 : 1; 
            SASSERT(wn - inc >= 1);            
            cf.m_weight += inc;
            cn.m_weight -= inc;
            for (literal lit : get_clause(cf_idx)) {
                inc_reward(lit, inc);
            }
            if (cn.m_num_trues == 1) {
                inc_reward(to_literal(cn.m_trues), inc);
            }
        }
        // DEBUG_CODE(invariant(););
    }

    std::ostream& ddfw::display(std::ostream& out) const {
        unsigned num_cls = m_clauses.size();
        for (unsigned i = 0; i < num_cls; ++i) {
            out << get_clause(i) << " ";
            auto const& ci = m_clauses[i];
            out << ci.m_num_trues << " " << ci.m_weight << "\n";
        }
        unsigned num_vars = m_reward.size();
        for (unsigned v = 0; v < num_vars; ++v) {
            out << v << ": " << m_reward[v] << "\n";
        }
        out << "unsat vars: ";
        for (bool_var v : m_unsat_vars) {
            out << v << " ";
        }
        out << "\n";
        return out;
    }

    void ddfw::invariant() {
        // every variable in unsat vars is in a false clause.
        for (bool_var v : m_unsat_vars) {
            bool found = false;
            for (unsigned cl : m_unsat) {
                for (literal lit : get_clause(cl)) {
                    if (lit.var() == v) { found = true; break; }
                }
                if (found) break;
            }
            if (!found) IF_VERBOSE(0, verbose_stream() << "unsat var not found: " << v << "\n"; );
            VERIFY(found);
        }
        return;
        unsigned num_vars = m_reward.size();
        for (unsigned v = 0; v < num_vars; ++v) {
            int reward = 0;
            literal lit(v, !m_values[v]);
            for (unsigned j : m_use_list[lit.index()]) {
                clause_info const& ci = m_clauses[j];
                if (ci.m_num_trues == 1) {
                    SASSERT(lit == to_literal(ci.m_trues));
                    reward -= ci.m_weight;
                }
            }
            for (unsigned j : m_use_list[(~lit).index()]) {
                clause_info const& ci = m_clauses[j];
                if (ci.m_num_trues == 0) {
                    reward += ci.m_weight;
                }                
            }
            IF_VERBOSE(0, if (reward != m_reward[v]) verbose_stream() << v << " " << reward << " " << m_reward[v] << "\n");
            SASSERT(m_reward[v] == reward);
        }
        for (auto const& ci : m_clauses) {
            SASSERT(ci.m_weight > 0);
        }
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            clause_info const& ci = m_clauses[i];
            bool found = false;
            for (literal lit : get_clause(i)) {
                if (is_true(lit)) found = true;
            }
            SASSERT(ci.is_true() == found);
            SASSERT(found == !m_unsat.contains(i));
        }
        // every variable in a false clause is in unsat vars
        for (unsigned cl : m_unsat) {
            for (literal lit : get_clause(cl)) {
                SASSERT(m_unsat_vars.contains(lit.var()));
            }
        }
    }

    void ddfw::updt_params(params_ref const& _p) {
        sat_params p(_p);
        m_config.m_init_clause_weight = p.ddfw_init_clause_weight();
        m_config.m_use_reward_zero_pct = p.ddfw_use_reward_pct();
    }
    
}

