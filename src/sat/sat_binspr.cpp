/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_binspr.cpp

  Abstract:
   
    Inprocessing step for creating SPR binary clauses.

  Author:

    Nikolaj Bjorner, Marijn Heule 2019-4-29

  Notes:


  L = { lit1, lit2 }
  G := { touched_L(C) |  C in F and C intersects with L, and not F|L |-_unit untouch_L(C) }
  G & ~L is satisfiable
  ------------
  Learn ~lit1 or ~lit2


Marijn's version:

  L = { lit1, lit2 }
  alpha = L + units in F|L
  G := { touched_alpha(C) |  C in F and C intersects with L, and not F|L |-_unit untouch_alpha(C) }
  G & ~L is satisfiable
  ---------------------
  Learn ~L

    


  Alternative:   

  for p in literals:
      push(1)
      propagate(p)
      candidates = literals \ units
      for (C or p) in use(p) and candidates != empty:
          push(1)
          propagate(~C)
          if inconsistent():
             learn C (subsumes C or p)
          else:
             candidates' := C union ~(consequencs of propagate(~C))
             candidates  := candidates' intersect candidates
          pop(1)
      for q in candidates:
          add (~q or ~p)
      pop(1) 

  The idea is that all clauses using p must satisfy 
      q in C or F|pq |-1 untouched(C)
  The clauses that contain q are not restricted: We directly create G := (~p or ~q) & q, which is satisfiable
  Let pqM |= F, we claim then that ~pqM |= F 
  
  - every clause (C or q) that contains q is satisfied by ~pqM
  - every clause (C or p) that does not contain q positively, but contains p satisfies F|pq |-1 untouched(C)
    Therefore pqM |= untouched(C) and therefore already M |= untouched(C)
  - all other clauses are satisfied by pqM, but contain neither p, nor q, 
    so it is already the case that M satisfies the clause.

  Alternative:

  for p in literals:
      push(1)
      propagate(p)
      candidates = {}
      for (C or p) in use(p):
          push(1)
          propagate(~C)
          if inconsistent():
             learn C (subsumes C or p)
          else:
             candidates := candicates union C union ~(consequencs of propagate(~C))
          pop(1)
      for q in candidates:
          push(1)
          propagate(q)
          incons := true
          for (C or p) in use(p) and incons:
              push(1)
              propagate(~C)
              incons := inconsistent()
              pop(1)
          pop(1)
          if incons:
             add (~p or ~q)
      pop(1) 

  The idea is similar to the previous alternative, but it allows a candidate to
  not be directly unit derivable in all clauses C or p, but could be a failed literal
  under the assumption ~C. 
  The motivation for this variant is that it is unlikely that we need failed literals to
  close both (C_1 or p),..., (C_n or p) for all clauses containing p.

  Alternative:

  F, p |- ~u, 
  F, q |- ~v, 
  { p, v } u C in F
  { q, u } u D in F
  
  Then use { p, ~u, q, ~v } as alpha, L = { p, q }
  
  for u in ~consequences of p:
      for (u u D) in use(u):
          for q in D, unassigned:
              for v in ~consequences of q:
                  for (v u C) in use(v):
                      if p in C:
                         check_spr(p, q, u, v)


  for u in ~consequences of p:
      for (u u D) in use(u):
          for q in D, unassigned:              
              check_spr(p, ~u, q)

  what is ~s?

  check_spr(p, ~u, q):
      for v in ~consequences(q) | ({p, v} u C) in use(v):
          check_spr(p, q, u, v)                

  --*/

#include "sat/sat_binspr.h"
#include "sat/sat_solver.h"
#include "sat/sat_big.h"

namespace sat {

    struct binspr::report {
        binspr& m_binspr;
        stopwatch m_watch;
        report(binspr& b): 
            m_binspr(b) {
            m_watch.start();
        }
        ~report() {
            m_watch.stop();
            unsigned nb = m_binspr.m_bin_clauses;
            IF_VERBOSE(2, verbose_stream() << " (sat-binspr :binary " << nb << m_watch << ")\n");
        }            
    };

    void binspr::operator()() {
        unsigned num = s.num_vars();
        m_bin_clauses = 0;

        report _rep(*this);
        m_use_list.reset();
        m_use_list.reserve(num*2);
        for (clause* c : s.m_clauses) {
            if (!c->frozen() && !c->was_removed()) { 
                for (literal lit : *c) {
                    m_use_list[lit.index()].push_back(c);
                }
            }
        }
        TRACE("sat", s.display(tout););
        algorithm1();
    }

    void binspr::algorithm1() {
        unsigned num_lits = 2 * s.num_vars();
        m_mark.reserve(num_lits, false);
        m_mark2.reserve(num_lits, false);
        IF_VERBOSE(0, verbose_stream() << "single lookahead\n");
        for (unsigned l_idx = 0; l_idx < num_lits && !s.inconsistent(); ++l_idx) {
            s.checkpoint();
            literal lit = to_literal(l_idx);
            if (is_used(lit)) {
                check_spr_single_lookahead(lit);
            }       
        } 
    }

    void binspr::algorithm2() {
        IF_VERBOSE(0, verbose_stream() << "algorithm2\n");
        unsigned num_lits = 2 * s.num_vars();
        for (unsigned l_idx = 0; l_idx < num_lits && !s.inconsistent(); ++l_idx) {
            s.checkpoint();
            literal p = to_literal(l_idx);
            if (is_used(p) && s.value(p) == l_undef) {
                s.push();
                s.assign_scoped(p);
                unsigned sz_p = s.m_trail.size();
                s.propagate(false);
                if (s.inconsistent()) {
                    s.pop(1);
                    s.assign_unit(~p);
                    s.propagate(false);
                    continue;
                }
                for (unsigned i = sz_p; !s.inconsistent() && i < s.m_trail.size(); ++i) {
                    literal u = ~s.m_trail[i];
                    for (clause* cp : m_use_list[u.index()]) {
                        for (literal q : *cp) {
                            if (s.value(q) == l_undef && !s.inconsistent()) {
                                s.push();
                                s.assign_scoped(q);
                                unsigned sz_q = s.m_trail.size();
                                s.propagate(false);
                                if (s.inconsistent()) {
                                    // learn ~p or ~q
                                    s.pop(1);
                                    block_binary(p, q, true);
                                    s.propagate(false);
                                    sz_p = s.m_trail.size();
                                    continue;
                                }
                                bool found = false;
                                for (unsigned j = sz_q; !found && j < s.m_trail.size(); ++j) {
                                    literal v = ~s.m_trail[j];
                                    for (clause* cp2 : m_use_list[v.index()]) {
                                        if (cp2->contains(p)) {
                                            if (check_spr(p, q, u, v)) {
                                                found = true;
                                                break;
                                            }
                                        }
                                    }
                                }
                                s.pop(1);
                                if (found) {
                                    block_binary(p, q, false);
                                    s.propagate(false);
                                    sz_p = s.m_trail.size();
                                }
                            }
                        }
                    }
                }
                s.pop(1);
            }
        }               
    }

    void binspr::check_spr_single_lookahead(literal lit) {
        s.push();

        s.assign_scoped(lit);
        s.propagate(false);
        
        if (s.inconsistent()) {
            s.pop(1);
            s.assign_unit(~lit);
            s.propagate(false);
            return;
        }
        
        IF_VERBOSE(0, verbose_stream() << "initialize candidates " << lit << "\n");
        m_may_candidates.reset();        
        m_must_candidates.reset();        
        for (watched const& w : s.get_wlist(~lit)) {
            if (s.inconsistent()) break;
            if (w.is_binary_non_learned_clause()) {
                literal lits[2] = { w.get_literal(), null_literal };
                collect_candidates(lit, lits, lits + 1);
            }
        }
        for (clause* cp : m_use_list[lit.index()]) {
            if (s.inconsistent()) break;
            collect_candidates(lit, cp->begin(), cp->end());
        }
        for (literal lit2 : m_must_candidates) {
            block_binary(lit, lit2, false);
            m_mark[lit2.index()] = false;
        } 
        IF_VERBOSE(0, 
                   verbose_stream() << m_may_candidates.size()  << ": " << m_may_candidates  << "\n";
                   verbose_stream() << m_must_candidates.size() << ": " << m_must_candidates << "\n";);

        s.propagate(false);        
        for (literal lit2 : m_may_candidates) {
            if (!m_mark[lit2.index()]) continue;                
            m_mark[lit2.index()] = false;
            if (!s.inconsistent()) check_spr(lit, lit2);
        }

        s.pop(1);
        s.propagate(false);
        
    }

    void binspr::collect_candidates(literal lit, literal const* begin, literal const* end) {
        unsigned sz = s.m_trail.size();
        literal const* it = begin;
        s.push();
        for (; it != end; ++it) {
            literal lit2 = *it;
            if (lit2 != lit && s.value(lit2) != l_false) {
                s.assign_scoped(~lit2);
            }
        }
        s.propagate(false);
        IF_VERBOSE(0, verbose_stream() << "trail " << lit << ": " << s.m_trail << "\n";);

        if (s.inconsistent()) {
            s.pop(1);
            strengthen_clause(lit, begin, end);
            return;
        }

        bool first = m_may_candidates.empty();
        for (unsigned i = sz; i < s.m_trail.size(); ++i) {
            literal lit2 = ~s.m_trail[i];
            if (!m_mark[lit2.index()]) {
                m_may_candidates.push_back(lit2);
                m_mark[lit2.index()] = true;
                if (first) m_must_candidates.push_back(lit2);
            }
            m_mark2[lit2.index()] = true;
        }
        if (!first) {
            unsigned j = 0;
            for (literal l : m_must_candidates) {
                if (m_mark2[l.index()]) m_must_candidates[j++] = l;
            }
            m_must_candidates.shrink(j);
        }
        for (unsigned i = sz; i < s.m_trail.size(); ++i) {
            literal lit2 = ~s.m_trail[i];
            m_mark2[lit2.index()] = false;
        }
        s.pop(1);
    }

    void binspr::strengthen_clause(literal lit, literal const* begin, literal const* end) {
        literal_vector lits;
        for (literal const* it = begin; it != end; ++it) {
            if (*it != lit) lits.push_back(*it);
        }
        IF_VERBOSE(0, verbose_stream() << "TBD clause strengthened " << lits << "\n");
#if 0
        s.mk_clause(lits.size(), lits.c_ptr(), true);
        s.propagate(false);
#endif
        
    }

    void binspr::double_lookahead() {
        unsigned num = s.num_vars();
        unsigned offset = m_stopped_at;
        for (unsigned i = 0, count = 0; i < num && count <= m_limit1 && !s.inconsistent(); ++i) {
            s.checkpoint();
            bool_var v = (offset + i) % num;
            m_stopped_at = v;
            if (s.value(v) == l_undef && !s.was_eliminated(v)) {
                literal lit1(v, false);
                if (is_used(lit1)) check_spr(lit1);            
                if (!s.inconsistent() && s.value(v) == l_undef && is_used(~lit1)) check_spr(~lit1);            
                ++count;
            }
        }        
        m_limit1 *= 2;
        m_limit2 *= 2;
    }

    bool binspr::is_used(literal lit) const {
        return !m_use_list[lit.index()].empty() || !s.get_wlist(~lit).empty();
    }
    
    void binspr::check_spr(literal lit1) {
        TRACE("sat", tout << lit1 << "\n";);
        s.push();
        s.assign_scoped(lit1);
        s.propagate(false);
        unsigned num = s.num_vars() - lit1.var() - 1;
        unsigned start = s.rand()(); 
        // break symmetries: only consider variables larger than lit1
        for (unsigned i = 0, count = 0; i < num && count <= m_limit2 && !s.inconsistent(); ++i) {
            bool_var v = ((i + start) % num) + lit1.var() + 1;
            s.checkpoint();
            if (s.value(v) == l_undef && !s.was_eliminated(v)) {
                literal lit2(v, false);
                check_spr(lit1, lit2);            
                if (!s.inconsistent() && s.value(lit2) == l_undef) check_spr(lit1, ~lit2);            
                ++count;
            }
        }
        if (s.inconsistent()) {
            s.pop(1);
            s.assign_unit(~lit1);
        }
        else {
            s.pop(1);
        }
        s.propagate(false);
    }

    // TBD: do we really need ~u, ~v? They are implied by p, q.
    bool binspr::check_spr(literal p, literal q, literal u, literal v) {
        SASSERT(s.value(p) == l_true);
        SASSERT(s.value(q) == l_true);
        SASSERT(s.value(u) == l_false);
        SASSERT(s.value(v) == l_false);
        init_g(p, q, u, v);
        literal lits[4] = { p, q, ~u, ~v };
        for (unsigned i = 0; g_is_sat() && i < 4; ++i) {
            binary_are_unit_implied(lits[i]);
            clauses_are_unit_implied(lits[i]);
        }
        return g_is_sat();
    }

    void binspr::binary_are_unit_implied(literal p) {
        for (watched const& w : s.get_wlist(~p)) {
            if (!g_is_sat()) {
                break;
            }
            if (!w.is_binary_non_learned_clause()) {
                continue;
            }            

            clear_alpha();
            VERIFY(touch(p));
            literal lit = w.get_literal();
            SASSERT(lit != p);
            
            if (touch(lit)) {
                add_touched();
                continue;
            }

            bool inconsistent = (s.value(lit) == l_true);
            if (s.value(lit) == l_undef) {
                s.push();
                s.assign_scoped(~lit);
                s.propagate(false);
                inconsistent = s.inconsistent();
                s.pop(1);
            }

            if (!inconsistent) {            
                add_touched();
            }
        }
    }

    void binspr::clauses_are_unit_implied(literal p) {
        for (clause* cp : m_use_list[p.index()]) {
            if (!g_is_sat()) break;
            clause_is_unit_implied(*cp);
        }
    }

    void binspr::clause_is_unit_implied(clause const& c) {
        s.push();
        clear_alpha();
        for (literal lit : c) {
            if (touch(lit)) {
                continue;
            }
            else if (s.value(lit) == l_true) {
                s.pop(1);
                return;
            }
            else if (s.value(lit) != l_false) {
                s.assign_scoped(~lit);
            }
        }
        s.propagate(false);
        bool inconsistent = s.inconsistent();
        s.pop(1);
        if (!inconsistent) {
            add_touched();
        }
    }

    void binspr::check_spr(literal lit1, literal lit2) {
        s.push();
        s.assign_scoped(lit2);        
        s.propagate(false);
        IF_VERBOSE(3, verbose_stream() << "check-spr: " << lit1 << " " << lit2 << ": " << s.m_trail << "\n");
        bool learned = s.inconsistent();
        init_g();
        if (!s.inconsistent()) {
            binary_are_unit_implied (lit1, lit2);
            clauses_are_unit_implied(lit1, lit2);
            binary_are_unit_implied (lit2, lit1);
            clauses_are_unit_implied(lit2, lit1);
        }
        s.pop(1);
        if (g_is_sat()) {
            block_binary(lit1, lit2, learned);
            s.propagate(false);
        }
    }

    void binspr::block_binary(literal lit1, literal lit2, bool learned) {
        IF_VERBOSE(1, verbose_stream() << "SPR: " << learned << " " << ~lit1 << " " << ~lit2 << "\n");
        TRACE("sat", tout << "SPR: " << learned << " " << ~lit1 << " " << ~lit2 << "\n";);
        s.mk_clause(~lit1, ~lit2, learned);
        ++m_bin_clauses;
    }

    void binspr::binary_are_unit_implied(literal lit1, literal lit2) {
        for (watched const& w : s.get_wlist(~lit1)) {
            if (!g_is_sat()) {
                break;
            }
            if (!w.is_binary_non_learned_clause()) {
                continue;
            }            
            literal lit3 = w.get_literal();
            SASSERT(lit3 != lit1);
            
            if (lit2.var() == lit3.var()) {
                g_add_binary(lit1, lit2, lit2 != lit3);
                continue;
            }

            bool inconsistent = (s.value(lit3) == l_true);
            if (s.value(lit3) == l_undef) {
                s.push();
                s.assign_scoped(~lit3);
                s.propagate(false);
                inconsistent = s.inconsistent();
                s.pop(1);
            }

            if (!inconsistent) {            
                g_add_unit(lit1, lit2);
            }
        }
    }

    void binspr::clauses_are_unit_implied(literal lit1, literal lit2) {        
        for (clause* cp : m_use_list[lit1.index()]) {
            if (!g_is_sat()) break;
            clause_is_unit_implied(lit1, lit2, *cp);
        }
    }

    void binspr::clause_is_unit_implied(literal lit1, literal lit2, clause& c) {
        literal lit3 = null_literal;
        s.push();
        for (literal lit : c) {
            if (lit == lit1) {
                // found occurrence
            }
            else if (lit.var() == lit2.var()) {
                lit3 = lit;
            }
            else if (s.value(lit) == l_true) {
                s.pop(1);
                return;
            }
            else if (s.value(lit) != l_false) {
                s.assign_scoped(~lit);
            }
        }
        s.propagate(false);
        bool inconsistent = s.inconsistent();
        s.pop(1);
        if (inconsistent) {
            // no op
        }
        else if (lit3 == null_literal) {
            g_add_unit(lit1, lit2);
        }
        else {
            g_add_binary(lit1, lit2, lit2 != lit3);
        }
    }

    void binspr::g_add_unit(literal lit1, literal lit2) {
        if (lit1.var() < lit2.var()) {
            m_state &= 0x2;
        }
        else {
            m_state &= 0x4;
        }
    }

    void binspr::g_add_binary(literal lit1, literal lit2, bool flip2) {
        bool flip1 = false;
        if (lit1.var() > lit2.var()) { std::swap(flip1, flip2); }
        m_state &= ((flip1?0x5:0xA) | (flip2?0x3:0xC)); 
    }

    // 0 -> 10
    // 1 -> 01
    // * -> 11
    // 00 -> 1000
    // 10 -> 0100
    // 01 -> 0010
    // 11 -> 0001
    // *1 -> 00110011
    // *0 -> 11001100
    // 0* -> 10101010
    // 1* -> 01010101
    // **1 -> 00001111
    // **0 -> 11110000

    /**
       \brief create masks (lsb is left)
       i = 0: 1010101010101010
       i = 1: 1100110011001100
       i = 2: 1111000011110000
     */
    unsigned binspr::mk_mask(unsigned i) {
        // variable number i is false.
        unsigned mask0 = (1 << (1 + (1 << i))) - 1;  // 2^i bits of ones
        unsigned pos = 1 << i;                       // how many bits in mask 
        unsigned mask = mask0;
        while (pos < 32) {
            mask |= (mask0 << pos);
            pos += 2*(i+1);
        }
        return mask;
    }

    void binspr::mk_masks() {
        for (unsigned i = 0; i < max_lits; ++i) {
            m_false[i] = mk_mask(i);
            m_true[i]  = m_false[i] << (1 << i);
        }
    }

    /**
       \brief create Boolean function table
       corresponding to disjunction of literals
    */
    
    void binspr::add_touched() {
        unsigned mask = 0;
        for (unsigned i = 0; i < 4; ++i) {
            switch (m_vals[i]) {
            case l_true:
                mask |= m_true[i];
                break;
            case l_false:
                mask |= m_false[i];
                break;
            default:
                break;
            }
            ++i;
        }
        IF_VERBOSE(0, display_mask(verbose_stream(), mask););
        m_state &= mask;
    }

    void binspr::init_g(literal p, literal q, literal u, literal v) {
        m_p = p.var();
        m_q = q.var();
        m_u = u.var();
        m_v = v.var();
        m_state = 0;
        clear_alpha();
        VERIFY(touch(~p));
        VERIFY(touch(~q));
        add_touched();
    }

    void binspr::clear_alpha() {
        m_vals[0] = m_vals[1] = m_vals[2] = m_vals[3] = l_undef;
    }

    bool binspr::touch(literal p) {
        bool_var v = p.var();
        if (v == m_p) m_vals[0] = to_lbool(p.sign());
        else if (v == m_q) m_vals[1] = to_lbool(p.sign());
        else if (v == m_u) m_vals[2] = to_lbool(p.sign());
        else if (v == m_v) m_vals[3] = to_lbool(p.sign());
        else return false;
        return true;
    }

    void binspr::display_mask(std::ostream& out, unsigned mask) {
        if (m_p
    }


}

