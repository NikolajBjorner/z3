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

#include "util/luby.h"
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
            if (should_reinit_weights()) do_reinit_weights();
            else if (do_flip()) ;
            else if (should_restart()) do_restart();
            else shift_weights();                       
        }
        return m_min_sz == 0 ? l_true : l_undef;
    }

    void ddfw::log() {
        double sec = m_stopwatch.get_current_seconds();        
        double kflips_per_sec = (m_flips - m_last_flips) / (1000.0 * sec);
        IF_VERBOSE(0, verbose_stream() 
                   << " unsat "   << m_min_sz
                   << " models " << m_models.size()
                   << " kflips/sec " << kflips_per_sec
                   << " vars: "   << m_reward.size() 
                   << " flips: "  << m_flips 
                   << " restarts: " << m_restart_count
                   << " reinits: " << m_reinit_count
                   << " unsat_vars " << m_unsat_vars.size()
                   << " shifts: " << m_shifts << "\n");
        m_stopwatch.start();
        m_last_flips = m_flips;
    }

    bool ddfw::do_flip() {
        bool_var v = pick_var();
        if (m_reward[v] > 0 || (m_reward[v] == 0 && m_rand(100) <= m_config.m_use_reward_zero_pct)) {
            flip(v);
            if (m_unsat.size() <= m_min_sz) save_best_values();
            return true;
        }
        return false;
    }

    bool_var ddfw::pick_var() {
        if (m_config.m_use_heap) {
            return m_heap.min_value();
        }
        else {
            double sum_pos = 0, sum_zero = 0;
            for (bool_var v : m_unsat_vars) {
                int r = m_reward[v];
                if (r > 0) {
                    sum_pos += r;
                }
                else if (r == 0) {
                    sum_zero++;
                }
            }
            if (sum_pos > 0) {
                double lim_pos = ((double) m_rand() / (1.0 + m_rand.max_value())) * sum_pos;                
                for (bool_var v : m_unsat_vars) {
                    int r = m_reward[v];
                    if (r > 0) {
                        lim_pos -= r;
                        if (lim_pos <= 0) {
                            return v;
                        }
                    }
                }
            }
            if (sum_zero > 0) {
                double lim_zero = ((double) m_rand() / (1.0 + m_rand.max_value())) * sum_zero;
                for (bool_var v : m_unsat_vars) {
                    int r = m_reward[v];
                    if (r == 0) {
                        lim_zero -= 1;
                        if (lim_zero <= 0) {
                            return v;
                        }
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
        m_bias.reserve(m_reward.size());
        m_make_count.reserve(m_reward.size(), 0);
        for (unsigned v = 0; v < m_reward.size(); ++v) {
            m_values[v] = (m_rand() % 2 == 0);
        }
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            clause_info& ci = m_clauses[i];
            ci.m_weight = m_config.m_init_clause_weight;
        }
        init_clause_data();
        flatten_use_list();

        m_reinit_count = 0;
        m_reinit_next = m_config.m_reinit_inc;
        m_reinit_next_reset = 1;

        m_restart_count = 0;
        m_restart_next = m_config.m_restart_base*2;

        m_min_sz = m_unsat.size();
        m_flips = 0;
        m_last_flips = 0;
        m_shifts = 0;
        m_stopwatch.start();
    }

    void ddfw::flatten_use_list() {
        m_use_list_index.reset();
        m_flat_use_list.reset();
        for (auto const& ul : m_use_list) {
            m_use_list_index.push_back(m_flat_use_list.size());
            m_flat_use_list.append(ul);
        }
        m_use_list_index.push_back(m_flat_use_list.size());
    }


    void ddfw::flip(bool_var v) {
        ++m_flips;
        literal lit = literal(v, !m_values[v]);
        literal nlit = ~lit;
        SASSERT(is_true(lit));
        for (unsigned cls_idx : use_list(*this, lit)) {
            clause_info& ci = m_clauses[cls_idx];
            ci.del(lit);
            unsigned w = ci.m_weight;
            // cls becomes false: flip any variable in clause to receive reward w
            switch (ci.m_num_trues) {
            case 0: {
                m_unsat.insert(cls_idx);
                clause const& c = get_clause(cls_idx);
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
        for (unsigned cls_idx : use_list(*this, nlit)) {
            clause_info& ci = m_clauses[cls_idx];             
            unsigned w = ci.m_weight;
            // the clause used to have a single true (pivot) literal, now it has two.
            // Then the previous pivot is no longer penalized for flipping.
            switch (ci.m_num_trues) {
            case 0: {
                m_unsat.remove(cls_idx);   
                clause const& c = get_clause(cls_idx);
                for (literal l : c) {
                    dec_reward(l, w);
                    dec_make(l);
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

    void ddfw::do_reinit_weights() {
        log();

        if (m_reinit_count % 2 == 0) { 
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
            m_reinit_next_reset += m_reinit_count;                        
        }
        init_clause_data();   
        ++m_reinit_count;
        m_reinit_next += m_reinit_count * m_config.m_reinit_inc;
    }

    void ddfw::init_clause_data() {
        if (m_config.m_use_heap) {
            m_heap.clear();
            m_heap.reserve(m_reward.size());
            for (unsigned v = 0; v < m_reward.size(); ++v) {
                m_heap.insert(v);
            }
        }
        else {
            // inc_make below.
        }
        for (unsigned& c : m_make_count) {
            c = 0;
        }
        for (int& r : m_reward) {
            r = 0;
        }
        m_unsat_vars.reset();
        m_unsat.reset();
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto& ci = m_clauses[i];
            clause const& c = get_clause(i);
            ci.m_trues = 0;
            ci.m_num_trues = 0;
            for (literal lit : c) {
                if (is_true(lit)) {
                    ci.add(lit);
                }
            }
            switch (ci.m_num_trues) {
            case 0:
                for (literal lit : get_clause(i)) {
                    inc_reward(lit, ci.m_weight);
                    inc_make(lit);
                }
                m_unsat.insert(i);
                break;
            case 1:
                dec_reward(to_literal(ci.m_trues), ci.m_weight);
                break;
            default:
                break;
            }
        }
    }

    bool ddfw::should_restart() {
        return m_flips > m_restart_next;
    }

    void ddfw::do_restart() {        
        reinit_values();
        init_clause_data();
        m_restart_next += m_config.m_restart_base*get_luby(++m_restart_count);
    }

    /**
       \brief the higher the bias, the lower the probability to deviate from the value of the bias 
       during a restart.
        bias  = 0 -> flip truth value with 50%
       |bias| = 1 -> flip with 25% probability
       |bias| = 2 -> flip with 12% probaility
       etc
    */
    void ddfw::reinit_values() {
        for (unsigned i = 0; i < m_values.size(); ++i) {
            int b = m_bias[i];
            if (0 == (m_rand() % (1 + abs(b)))) {
                m_values[i] = (m_rand() % 2) == 0;
            }
            else {
                m_values[i] = m_bias[i] > 0;
            }
        }        
    }

    void ddfw::save_best_values() {
        if (m_unsat.size() < m_min_sz) {
            m_models.reset();
            for (int& b : m_bias) {
                if (abs(b) > 3) {
                    b = b > 0 ? 3 : -3;
                }
            }
        }
        m_model.reserve(m_values.size());
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_model[i] = to_lbool(m_values[i]);
        }
        m_min_sz = m_unsat.size();
        unsigned h = model_hash(m_values);
        if (!m_models.contains(h)) {
            for (unsigned i = 0; i < m_values.size(); ++i) {
                m_bias[i] += m_values[i] ? 1 : -1;
            }
            m_models.insert(h, m_values);
            if (m_models.size() > m_config.m_max_num_models) {
                m_models.erase(m_models.begin()->m_key);
            }
        }
    }

    unsigned ddfw::model_hash(svector<bool> const& m) const {
        return string_hash(reinterpret_cast<char const*>(m.c_ptr()), m.size()*sizeof(bool), 11);
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

