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
  G is satisfiable
  ------------
  Learn ~lit1 or ~lit2


Marijn's version:

  L = { lit1, lit2 }
  alpha = L + units in F|L
  G := { touched_alpha(C) |  C in F and C intersects with L, and not F|L |-_unit untouch_alpha(C) }
  G is satisfiable
  ---------------------
  Learn ~lit1 or ~lit2

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

  for p in literals:
      push(1)
      alpha := propagate(p)
      for r in alpha u { p }
          for (C or r) in use(r):
              push(1)
              propagate(~C)
              .... TBD
          pop(1)
      ... TBD
      pop(1) 


  Alternative:
  
  Candidates = literals
  for p in literals: 
      push(1)
      propagate(p)
      for (C or p) in use(p):
          push(1)
          propagate(~C)
          if (!inconsistent()): 
             for q in Candidates, q is unassigned
                 push(1)
                 propagate(q)
                 if (!inconsistent()):
                    update G, Candidates for C or p
                 pop(1)
             for q in C or ~q in C, q in Candidates, q != p
                 update G, Candidates for C or p or q or C or p or ~q
          pop(1)
      for (q, G) in Candidates:
          for (C or q) in use(q):
              push(1)
              propagate(~C) (remove p if p in C)
              if (!inconsistent):
                  update G, Candidates for C or q
              pop(1)
      pop(1)

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
            if (!c->frozen()) { 
                for (literal lit : *c) {
                    m_use_list[lit.index()].push_back(c);
                }
            }
        }
        TRACE("sat", s.display(tout););
        single_lookahead();
    }

    void binspr::single_lookahead() {
        unsigned num = s.num_vars();
        m_mark.reserve(s.num_vars() * 2, false);
        IF_VERBOSE(0, verbose_stream() << "single lookahead\n");
        for (bool_var v = 0; v < num && !s.inconsistent(); ++v) {
            s.checkpoint();
            literal lit(v, false);
            if (!is_used(lit)) continue;
            check_spr_single_lookahead(lit);
            if (s.inconsistent()) break;
            check_spr_single_lookahead(~lit);
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
        s.push();
        for (; begin != end; ++begin) {
            literal lit2 = *begin;
            if (lit2 != lit && s.value(lit2) != l_false) {
                s.assign_scoped(~lit2);
            }
        }
        s.propagate(false);

        if (s.inconsistent()) {
            IF_VERBOSE(0, verbose_stream() << "TBD: can strengthen clause\n");
        }
        else {
            bool first = m_may_candidates.empty();
            for (unsigned i = sz; i < s.m_trail.size(); ++i) {
                literal lit2 = ~s.m_trail[i];
                if (!m_mark[lit2.index()]) {
                    m_may_candidates.push_back(lit2);
                    m_mark[lit2.index()] = true;
                    if (first) m_must_candidates.push_back(lit2);
                }
            }
            if (!first) {
                unsigned j = 0;
                for (literal l : m_must_candidates) {
                    if (m_mark[l.index()]) m_must_candidates[j++] = l;
                }
                m_must_candidates.shrink(j);
            }
        }
        s.pop(1);
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

    void binspr::check_spr(literal lit1, literal lit2) {
        s.push();
        reset_g(lit1, lit2);
        s.assign_scoped(lit2);
        s.propagate(false);
        if (s.inconsistent()) {
            s.pop(1);
            block_binary(lit1, lit2, true);
            s.propagate(false);
        }
        else if (binary_are_unit_implied(lit1, lit2) &&
                 binary_are_unit_implied(lit2, lit1) &&
                 clauses_are_unit_implied(lit1, lit2) &&
                 clauses_are_unit_implied(lit2, lit1)) {
            s.pop(1);
            block_binary(lit1, lit2, false);
            s.propagate(false);
        }
        else {
            s.pop(1);
        }
    }

    void binspr::block_binary(literal lit1, literal lit2, bool learned) {
        IF_VERBOSE(1, verbose_stream() << "SPR: " << learned << " " << ~lit1 << " " << ~lit2 << "\n");
        TRACE("sat", tout << "SPR: " << learned << " " << ~lit1 << " " << ~lit2 << "\n";);
        s.mk_clause(~lit1, ~lit2, learned);
        ++m_bin_clauses;
    }

    bool binspr::binary_are_unit_implied(literal lit1, literal lit2) {
        if (m_units.contains(lit1)) return true;
        for (watched const& w : s.get_wlist(~lit1)) {
            if (!w.is_binary_non_learned_clause()) {
                continue;
            }            
            literal lit3 = w.get_literal();
            SASSERT(lit3 != lit1);
            bool is_implied = true;
            if (lit3 == lit2) {
                is_implied = add_g(lit1, lit2);
            }
            else if (s.value(lit3) == l_true) {
                continue;
            }
            else if (s.value(lit3) == l_false) {
                return add_g(lit1);
            }
            else {
                s.push();
                s.assign_scoped(~lit3);
                s.propagate(false);
                is_implied = s.inconsistent() || add_g(lit1);
                TRACE("sat", tout << "check-prop " << is_implied << ": " << ~lit1 << " " << ~lit2 << ": " << lit1 << " " << lit3 << "\n";);
                s.pop(1);
            }
            if (!is_implied) {
                return false;
            }
        }
        return true;
    }

    void binspr::reset_g(literal lit1, literal lit2) {
        m_units.reset();
        m_bins.reset();
        m_bins.push_back(std::make_pair(~lit1, ~lit2));
    }

    // If we allow the case where G is non-empty there are the
    // following cases for clauses in G:
    // lit1
    // lit2
    // ~lit1
    // ~lit2
    //  (lit1 or  lit2)
    // (~lit1 or ~lit2)  **
    // (~lit1 or  lit2)
    //  (lit1 or ~lit2)
    // Given that satisfiability is checked with respect to **
    // additional clauses create either equivalence constraints
    // or units.
    bool binspr::add_g(literal lit1, literal lit2) {
        if (lit1 == lit2) {
            return add_g(lit1);
        }
        if (lit1 == ~lit2) {
            return true;
        }
        for (literal lit3 : m_units) {
            if (lit3 == lit1 || lit3 == lit2) return true;
            if (lit3 == ~lit1) return add_g(lit2);
            if (lit3 == ~lit2) return add_g(lit1);
        } 
        SASSERT(m_units.empty());
        if (lit1.var() > lit2.var()) {
            std::swap(lit1, lit2);
        }
        for (auto const& p : m_bins) {
            if (p.first == lit1  && p.second ==  lit2) return true;
            if (p.first == ~lit1 && p.second ==  lit2) return add_g(lit2);
            if (p.first == lit1  && p.second == ~lit2) return add_g(lit1);
            // if (p.first == ~lit1 && p.second == ~lit2) continue;            
        }
        m_bins.push_back(std::make_pair(lit1, lit2));
        return true;
    }

    bool binspr::add_g(literal lit1) {
        for (literal lit2 : m_units) {
            if (lit2 == lit1) return true;
            if (lit2 == ~lit1) return false;
        }
        // crappy propagation 
        m_units.push_back(lit1);
        unsigned j = 0, i = 0, sz = m_bins.size();
        for (; i < sz; ++i) {
            auto const& p = m_bins[i];
            if (p.first == ~lit1) {
                if (m_units.contains(~(p.second))) return false;           
                m_units.push_back(p.second);
            }
            else if (p.second == ~lit1) {
                if (m_units.contains(~(p.first))) return false;
                if (!m_units.contains(p.first)) m_units.push_back(p.first);
            }
            else {
                m_bins[j++] = p;
            }
        }
        m_bins.shrink(j);
        return true;
    }

    bool binspr::clauses_are_unit_implied(literal lit1, literal lit2) {        
        for (clause* cp : m_use_list[lit1.index()]) {
            if (!clause_is_unit_implied(lit1, lit2, *cp)) {
                return false;
            }
            if (m_units.contains(lit1)) {
                break;
            }
        }
        return true;
    }

    bool binspr::clause_is_unit_implied(literal lit1, literal lit2, clause& c) {
        if (c.was_removed()) {
            return true;
        }
        literal lit2_ = lit1;
        bool is_implied = false;
        bool found = false;
        s.push();
        for (literal lit : c) {
            if (lit == lit1) {
                found = true;
            }
            else if (lit.var() == lit2.var()) {
                lit2_ = lit2;
            }
            else if (s.value(lit) == l_true) {
                is_implied = true;
                break;
            }
            else if (s.value(lit) != l_false) {
                s.assign_scoped(~lit);
            }
        }
        if (!found && !is_implied) {
            std::cout << lit1 << " " << lit2 << " " << c << "\n";
        }
        SASSERT(found || is_implied);
        if (!is_implied) {
            s.propagate(false);
            is_implied = s.inconsistent();
            CTRACE("sat", !is_implied, tout << "not unit implied " << lit1 << " " << lit2 << ": " << c << "\n";);            
        }
        if (!is_implied) {
            is_implied = add_g(lit1, lit2_);
        }
        s.pop(1);
        TRACE("sat", tout << "is implied " << is_implied << " " << lit1 << " " << lit2 << " " << c << "\n";);
        return is_implied;
    }


}

