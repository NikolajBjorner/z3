/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#include "util/lp/nla_solver.h"
#include "util/map.h"
#include "util/lp/monomial.h"
#include "util/lp/lp_utils.h"
#include "util/lp/vars_equivalence.h"
#include "util/lp/factorization.h"

namespace nla {

struct solver::imp {

    typedef lp::lar_base_constraint lpcon;
    
   

    //fields    
    vars_equivalence                                                 m_vars_equivalence;
    vector<monomial>                                                 m_monomials;
    // maps the vector of the rooted monomial vars to the list of the indices of monomials having the same rooted monomial
    std::unordered_map<svector<lpvar>,
                       vector<index_with_sign>,
                       hash_svector>
                                                                     m_rooted_monomials_map;
    vector<svector<lpvar>>                                           m_vector_of_rooted_monomials;

    // this field is used for the push/pop operations
    unsigned_vector                                                  m_monomials_counts;
    lp::lar_solver&                                                  m_lar_solver;
    std::unordered_map<lpvar, svector<lpvar>>                        m_monomials_containing_var;
    // for every k 
    // for each i in m_rooted_monomials_containing_var[k]
    // m_vector_of_rooted_monomials[i] contains k
    std::unordered_map<lpvar, std::unordered_set<unsigned>>          m_rooted_monomials_containing_var;

    // A map from m_vector_of_rooted_monomials to a set
    // of sets of m_vector_of_rooted_monomials,
    // such that for every i and every h in m_vector_of_rooted_monomials[i]
    // m_vector_of_rooted_monomials[i] is a proper factor of m_vector_of_rooted_monomials[h]
    std::unordered_map<unsigned, std::unordered_set<unsigned>>       m_rooted_factor_to_product;
    
    // u_map[m_monomials[i].var()] = i
    u_map<unsigned>                                                  m_var_to_its_monomial;
    lp::explanation *                                                m_expl;
    lemma *                                                          m_lemma;
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
        :
        m_vars_equivalence([this](unsigned h){return vvr(h);}),
        m_lar_solver(s)
          // m_limit(lim),
          // m_params(p)
    {
    }


    rational vvr(unsigned j) const { return m_lar_solver.get_column_value_rational(j); }
    lp::impq vv(unsigned j) const { return m_lar_solver.get_column_value(j); }
    
    void add(lpvar v, unsigned sz, lpvar const* vs) {
        m_monomials.push_back(monomial(v, sz, vs));
        m_var_to_its_monomial.insert(v, m_monomials.size() - 1);
        TRACE("nla_solver", print_monomial(m_monomials.back(), tout););
    }
    
    void push() {
        TRACE("nla_solver",);
        m_monomials_counts.push_back(m_monomials.size());
    }


    void deregister_monomial_from_rooted_monomials (const monomial & m, unsigned i){
        rational sign = rational(1);
        svector<lpvar> vars = reduce_monomial_to_rooted(m.vars(), sign);
        NOT_IMPLEMENTED_YET();
    }

    void deregister_monomial_from_tables(const monomial & m, unsigned i){
        m_vars_equivalence.deregister_monomial_from_abs_vals(m, i);  
        deregister_monomial_from_rooted_monomials(m, i);     
    }
     
    void pop(unsigned n) {
        TRACE("nla_solver",);
        if (n == 0) return;
        unsigned new_size = m_monomials_counts[m_monomials_counts.size() - n];
        for (unsigned i = m_monomials.size(); i-- > new_size; ){
            deregister_monomial_from_tables(m_monomials[i], i);
        }
        m_monomials.shrink(new_size);
        m_monomials_counts.shrink(m_monomials_counts.size() - n);       
    }

    // return true if the monomial value is equal to the product of the values of the factors
    bool check_monomial(const monomial& m) {
        SASSERT(m_lar_solver.get_column_value(m.var()).is_int());
        const rational & model_val = m_lar_solver.get_column_value_rational(m.var());
        rational r(1);
        for (auto j : m) {
            r *= m_lar_solver.get_column_value_rational(j);
        }
        return r == model_val;
    }
    
    /**
     * \brief <here we have two monomials, i_mon and other_m, examined for "sign" equivalence>
     */

    bool values_are_different(lpvar j, rational const& sign, lpvar k) const {
        SASSERT(sign == 1 || sign == -1);
        return sign * m_lar_solver.get_column_value(j) != m_lar_solver.get_column_value(k);
    }

    void add_explanation_of_reducing_to_rooted_monomial(const monomial& m, expl_set & exp) const {
        m_vars_equivalence.add_explanation_of_reducing_to_rooted_monomial(m, exp);
    }

    void add_explanation_of_reducing_to_rooted_monomial(lpvar j, expl_set & exp) const {
        unsigned index = 0;
        if (!m_var_to_its_monomial.find(j, index))
            return; // j is not a var of a monomial
        add_explanation_of_reducing_to_rooted_monomial(m_monomials[index], exp);
    }


    
    std::ostream& print_monomial(const monomial& m, std::ostream& out) const {
        out << m_lar_solver.get_variable_name(m.var()) << " = ";
        for (unsigned k = 0; k < m.size(); k++) {
            out << m_lar_solver.get_variable_name(m.vars()[k]);
            if (k + 1 < m.size()) out << "*";
        }
        return out;
    }

    std::ostream& print_monomial(unsigned i, std::ostream& out) const {
        return print_monomial(m_monomials[i], out);
    }

    std::ostream& print_monomial_with_vars(unsigned i, std::ostream& out) const {
        return print_monomial_with_vars(m_monomials[i], tout);
    }

    template <typename T>
    std::ostream& print_product_with_vars(const T& m, std::ostream& out) const {
        for (unsigned k = 0; k < m.size(); k++) {
            out << m_lar_solver.get_variable_name(m.vars()[k]);
            if (k + 1 < m.size()) out << "*";
        }
        out << '\n';
        for (unsigned k = 0; k < m.size(); k++) {
            print_var(m.vars()[k], out);
        }
        return out;
        
    }
    std::ostream& print_monomial_with_vars(const monomial& m, std::ostream& out) const {
        out << m_lar_solver.get_variable_name(m.var()) << " = ";
        return print_product_with_vars(m, out);
    }

    
    std::ostream& print_explanation(std::ostream& out) const {
        for (auto &p : *m_expl) {
            m_lar_solver.print_constraint(p.second, out);
        }
        return out;
    }

    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        lp::lar_term t;
        t.add_coeff_var(a, j);
        t.add_coeff_var(b, k);
        m_lemma->push_back(ineq(cmp, t, rs));
    }

    void mk_ineq(lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        mk_ineq(rational(1), j, b, k, cmp, rs);
    }

    void mk_ineq(lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp) {
        mk_ineq(j, b, k, cmp, rational::zero());
    }

    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp) {
        mk_ineq(a, j, b, k, cmp, rational::zero());
    }

    void mk_ineq(const rational& a ,lpvar j, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        mk_ineq(a, j, rational(1), k, cmp, rs);
    }

    void mk_ineq(lpvar j, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        mk_ineq(j, rational(1), k, cmp, rs);
    }

    void mk_ineq(lpvar j, lp::lconstraint_kind cmp, const rational& rs) {
        lp::lar_term t;
        t.add_coeff_var(j);  
        m_lemma->push_back(ineq(cmp, t, rs));
    }

    void mk_ineq(const rational& a, lpvar j, lp::lconstraint_kind cmp, const rational& rs) {
        lp::lar_term t;
        t.add_coeff_var(a, j);  
        m_lemma->push_back(ineq(cmp, t, rs));
    }

    void mk_ineq(const rational& a, lpvar j, lp::lconstraint_kind cmp) {
        mk_ineq(a, j, cmp, rational::zero());
    }

    void mk_ineq(lpvar j, lpvar k, lp::lconstraint_kind cmp) {
        mk_ineq(rational(1), j, rational(1), k, cmp, rational::zero());
    }

    void mk_ineq(lpvar j, lp::lconstraint_kind cmp) {
        mk_ineq(j, cmp, rational::zero());
    }
    
    // the monomials should be equal by modulo sign but this is not so the model
    void fill_explanation_and_lemma_sign(const monomial& a, const monomial & b, rational const& sign) {
        expl_set expl;
        SASSERT(sign == 1 || sign == -1);
        add_explanation_of_reducing_to_rooted_monomial(a, expl);
        add_explanation_of_reducing_to_rooted_monomial(b, expl);
        m_expl->clear();
        m_expl->add(expl);
        TRACE("nla_solver",
              tout << "used constraints: ";
              for (auto &p : *m_expl)
                  m_lar_solver.print_constraint(p.second, tout); tout << "\n";
              );
        SASSERT(m_lemma->size() == 0);
        mk_ineq(rational(1), a.var(), -sign, b.var(), lp::lconstraint_kind::EQ, rational::zero());
        TRACE("nla_solver", print_lemma(tout););
    }

    // Replaces each variable index by the root in the tree and flips the sign if the var comes with a minus.
    // Also sorts the result.
    // 
    svector<lpvar> reduce_monomial_to_rooted(const svector<lpvar> & vars, rational & sign) const {
        svector<lpvar> ret;
        sign = 1;
        for (lpvar v : vars) {
            unsigned root = m_vars_equivalence.map_to_root(v, sign);
            SASSERT(m_vars_equivalence.is_root(root));
            ret.push_back(root);
        }
        std::sort(ret.begin(), ret.end());
        return ret;
    }


    // Replaces definition m_v = v1* .. * vn by
    // m_v = coeff * w1 * ... * wn, where w1, .., wn are canonical
    // representatives, that is the roots of the equivalence tree, under current equations.
    // 
    monomial_coeff canonize_monomial(monomial const& m) const {
        rational sign = rational(1);
        svector<lpvar> vars = reduce_monomial_to_rooted(m.vars(), sign);
        return monomial_coeff(vars, sign);
    }

    bool list_contains_one_to_refine(const std::unordered_set<unsigned> & to_refine_set,
                                     const vector<index_with_sign>& list_of_mon_indices) {
        for (const auto& p : list_of_mon_indices) {
            if (to_refine_set.find(p.m_i) != to_refine_set.end())
                return true;
        }
        return false;
    }


    // the value of the i-th monomial has to be equal to the value of the k-th monomial modulo sign
    // but it is not the case in the model
    void generate_sign_lemma(const vector<rational>& abs_vals, unsigned i, unsigned k, const rational& sign) {
        SASSERT(sign == rational(1) || sign == rational(-1));
        SASSERT(m_lemma->empty());
        TRACE("nla_solver",
              tout << "mon i=" << i << " = "; print_monomial_with_vars(m_monomials[i],tout);
              tout << '\n';
              tout << "mon k=" << k << " = "; print_monomial_with_vars(m_monomials[k],tout);
              tout << '\n';
              tout << "abs_vals="; print_vector(abs_vals, tout);
              );
        std::unordered_map<rational, vector<index_with_sign>> map;
        for (const rational& v : abs_vals) {
            map[v] = vector<index_with_sign>();
        }
  
        for (unsigned j : m_monomials[i]) {
            rational v = vvr(j);
            int s;
            if (v.is_pos()) {
                s = 1;
            } else {
                s = -1;
                v = -v; 
            };
            // v = abs(vvr(j))
            auto it = map.find(v);
            SASSERT(it != map.end());
            it->second.push_back(index_with_sign(j, rational(s)));
        } 

        for (unsigned j : m_monomials[k]) {
            rational v = vvr(j);
            rational s;
            if (v.is_pos()) {
                s = rational(1);
            } else {
                s = -rational(1);
                v = -v;
            };
            // v = abs(vvr(j))
            auto it = map.find(v);
            SASSERT(it != map.end());
            index_with_sign & ins = it->second.back();
            if (j != ins.m_i) {
                s *= ins.m_sign;
                mk_ineq(j, -s, ins.m_i, lp::lconstraint_kind::NE);
            }
            it->second.pop_back();
        } 

        mk_ineq(m_monomials[i].var(), -sign, m_monomials[k].var(), lp::lconstraint_kind::EQ);        
        TRACE("nla_solver", print_lemma(tout););
    }
    
    bool basic_sign_lemma_on_a_bucket_of_abs_vals(const vector<rational>& abs_vals, const vector<index_with_sign>& list){   
        rational sign = list[0].m_sign;
        rational val =  vvr(m_monomials[list[0].m_i].var());
        
        for (unsigned i = 1; i < list.size(); i++) {
            rational other_sign = list[i].m_sign;
            rational other_val =  vvr(m_monomials[list[i].m_i].var());
            if (val * sign != other_val * other_sign) {
                generate_sign_lemma(abs_vals, list[0].m_i, list[i].m_i, sign * other_sign);
                return true;
            }
        }
        return false;
    }
    
    /**
     * \brief <generate lemma by using the fact that -ab = (-a)b) and
     -ab = a(-b)
    */
    bool basic_sign_lemma() {
        for (const auto & p : m_vars_equivalence.monomials_by_abs_values()){
            if (basic_sign_lemma_on_a_bucket_of_abs_vals(p.first, p.second))
                return true;
        }
        return false;
    }

    bool is_set(unsigned j) const {
        return static_cast<unsigned>(-1) != j;
    }

    bool var_is_fixed_to_zero(lpvar j) const {
        return 
            m_lar_solver.column_has_upper_bound(j) &&
            m_lar_solver.column_has_lower_bound(j) &&
            m_lar_solver.get_upper_bound(j) == lp::zero_of_type<lp::impq>() &&
            m_lar_solver.get_lower_bound(j) == lp::zero_of_type<lp::impq>();
    }
    
    std::ostream & print_ineq(const ineq & in, std::ostream & out) const {
        m_lar_solver.print_term(in.m_term, out);
        out << " " << lp::lconstraint_kind_string(in.m_cmp) << " " << in.m_rs;
        return out;
    }

    std::ostream & print_var(lpvar j, std::ostream & out) const {
        bool is_monomial = false;
        for (const monomial & m : m_monomials) {
            if (j == m.var()) {
                is_monomial = true;
                print_monomial(m, out);
                out << " = " << vvr(j);;
                break;
            }
        }
        if (!is_monomial)
            out << m_lar_solver.get_variable_name(j) << " = " << vvr(j);
        out <<";";
        return out;
    }    

    std::ostream & print_lemma(std::ostream & out) const {
        auto &l = *m_lemma;
        out << "lemma: ";
        for (unsigned i = 0; i < l.size(); i++) {
            print_ineq(l[i], out);
            if (i + 1 < l.size()) out << " or ";
        }
        out << std::endl;
        std::unordered_set<lpvar> vars;
        for (auto & in: l) {
            for (const auto & p: in.m_term)
                vars.insert(p.var());
        }
        for (lpvar j : vars) {
            print_var(j, out);
        }
        out << "\n";
        return out;
    }
    
    // returns true if found
    bool find_monomial_of_vars(const svector<lpvar>& vars, monomial& m, rational & sign) const {
        auto it = m_rooted_monomials_map.find(vars);
        if (it == m_rooted_monomials_map.end()) {
            return false;
        }

        const index_with_sign & mi = *(it->second.begin());
        sign = mi.m_sign;
        m = m_monomials[mi.m_i];
        return true;
    }

    std::ostream & print_factorization(const factorization& f, std::ostream& out) const {
        for (unsigned k = 0; k < f.size(); k++ ) {
            print_var(f[k], out);
            if (k < f.size() - 1)
                out << "*";
        }
        return out << ", sign = " << f.sign();
    }
    
    struct factorization_factory_imp: factorization_factory {
        const imp&         m_imp;
        
        factorization_factory_imp(unsigned i_mon, const imp& s) :
            factorization_factory(i_mon,
                s.m_monomials[i_mon],
                s.canonize_monomial(s.m_monomials[i_mon])
                ),
                m_imp(s) { }
        
         bool find_monomial_of_vars(const svector<lpvar>& vars, monomial& m, rational & sign) const {
            auto it = m_imp.m_rooted_monomials_map.find(vars);
            if (it == m_imp.m_rooted_monomials_map.end()) {
                return false;
            }

            const index_with_sign & mi = *(it->second.begin());
            sign = mi.m_sign;
            m = m_imp.m_monomials[mi.m_i];
            return true;
        }
        
        
    };

    void explain(const factorization& f, expl_set exp) {
        for (lpvar k : f) {
            unsigned mon_index = 0;
            if (m_var_to_its_monomial.find(k, mon_index)) {
                add_explanation_of_reducing_to_rooted_monomial(m_monomials[mon_index], exp);
            }
        }
    }
    
    // here we use the fact
    // xy = 0 -> x = 0 or y = 0
    bool basic_lemma_for_mon_zero_from_monomial_to_factor(unsigned i_mon, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(i_mon, f, tout););
        lpvar mon_var = m_monomials[i_mon].var();
        if (!vvr(mon_var).is_zero() )
            return false;

        SASSERT(m_lemma->empty());
        mk_ineq(mon_var, lp::lconstraint_kind::NE);
        for (lpvar j : f) {
            mk_ineq(j, lp::lconstraint_kind::EQ);
        }
        expl_set e;
        add_explanation_of_factorization_and_set_explanation(i_mon, f, e);
        TRACE("nla_solver", print_lemma(tout););

        return true;
    }

    void set_expl(const expl_set & e) {
        m_expl->clear();
        for (lpci ci : e)
            m_expl->push_justification(ci);
    }

    void add_explanation_of_factorization(unsigned i_mon, const factorization& f, expl_set & e) {
        explain(f, e);
        // todo: it is an overkill, need to find shorter explanations
        add_explanation_of_reducing_to_rooted_monomial(m_monomials[i_mon], e);
    }

    void add_explanation_of_factorization_and_set_explanation(unsigned i_mon, const factorization& f, expl_set& e){
        add_explanation_of_factorization(i_mon, f, e);
        set_expl(e);
    }

    void trace_print_monomial_and_factorization(unsigned i_mon, const factorization& f, std::ostream& out) const {
        print_monomial(i_mon, out << "mon:  ") << "\n";
        out << "value: " << vvr(m_monomials[i_mon].var()) << "\n";
        print_factorization(f, out << "fact: ") << "\n";
    }
    // x = 0 or y = 0 -> xy = 0
    bool basic_lemma_for_mon_zero_from_factors_to_monomial(unsigned i_mon, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(i_mon, f, tout););
        if (vvr(m_monomials[i_mon].var()).is_zero())
            return false;
        unsigned zero_j = -1;
        for (lpvar j : f) {
            if (vvr(j).is_zero()) {
                zero_j = j;
                break;
            }
        }

        if (zero_j == static_cast<unsigned>(-1)) {
            return false;
        } 

        mk_ineq(zero_j, lp::lconstraint_kind::NE);
        mk_ineq(m_monomials[i_mon].var(), lp::lconstraint_kind::EQ);

        expl_set e;
        add_explanation_of_factorization_and_set_explanation(i_mon, f, e);
        TRACE("nla_solver", print_lemma(tout););
        return true;
    }

    
    bool basic_lemma_for_mon_zero(unsigned i_mon, const factorization& f) {
        return 
            basic_lemma_for_mon_zero_from_monomial_to_factor(i_mon, f) || 
            basic_lemma_for_mon_zero_from_factors_to_monomial(i_mon, f);
    }

    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1
    bool basic_lemma_for_mon_neutral_monomial_to_factor(unsigned i_mon, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(i_mon, f, tout););

        // todo : consider the case of just two factors
        lpvar mon_var = m_monomials[i_mon].var();
        const auto & mv = vvr(mon_var);
        const auto  abs_mv = abs(mv);
        
        if (abs_mv == rational::zero()) {
            return false;
        }
        lpvar jl = -1;
        for (lpvar j : f ) {
            if (abs(vvr(j)) == abs_mv) {
                jl = j;
                break;
            }
        }
        if (jl == static_cast<lpvar>(-1))
            return false;
        lpvar not_one_j = -1;
        for (lpvar j : f ) {
            if (j == jl) {
                continue;
            }
            if (abs(vvr(j)) != rational(1)) {
                not_one_j = j;
                break;
            }
        }

        if (not_one_j == static_cast<lpvar>(-1)) {
            return false;
        } 
        
        SASSERT(m_lemma->empty());
        // jl + mon_var != 0
        mk_ineq(jl, mon_var, lp::lconstraint_kind::NE);   
        
        // jl - mon_var != 0
        mk_ineq(jl, -rational(1), mon_var, lp::lconstraint_kind::NE);   

            // not_one_j = 1
        mk_ineq(not_one_j, lp::lconstraint_kind::EQ,  rational(1));   
        
        // not_one_j = -1
        mk_ineq(not_one_j, lp::lconstraint_kind::EQ, -rational(1));
        expl_set e;
        add_explanation_of_factorization_and_set_explanation(i_mon, f, e);
        TRACE("nla_solver", print_lemma(tout); );
        return true;
    }

    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x

    bool basic_lemma_for_mon_neutral_from_factors_to_monomial(unsigned i_mon, const factorization& f) {
        int sign = 1;
        lpvar not_one_j = -1;
        for (lpvar j : f){
            if (vvr(j) == rational(1)) {
                continue;
            }
            if (vvr(j) == -rational(1)) { 
                sign = - sign;
                continue;
            } 
            if (not_one_j == static_cast<lpvar>(-1)) {
                not_one_j = j;
                continue;
            }

            // if we are here then there are at least two factors with values different from one and minus one: cannot create the lemma
            return false;
        }

        expl_set e;
        add_explanation_of_factorization_and_set_explanation(i_mon, f, e);
        
        if (not_one_j == static_cast<lpvar>(-1)) {
     		// we can derive that the value of the monomial is equal to sign
            for (lpvar j : f){
                
                if (vvr(j) == rational(1)) {
                    mk_ineq(j, lp::lconstraint_kind::NE, rational(1));   
                } else if (vvr(j) == -rational(1)) {
                    mk_ineq(j, lp::lconstraint_kind::NE, -rational(1));   
                } 
            }
            mk_ineq(m_monomials[i_mon].var(), lp::lconstraint_kind::EQ, rational(sign));
            TRACE("nla_solver", print_lemma(tout););
            return true;
        }
        
        for (lpvar j : f){
            if (vvr(j) == rational(1)) {
                mk_ineq(j, lp::lconstraint_kind::NE, rational(1));   
            } else if (vvr(j) == -rational(1)) { 
                mk_ineq(j, lp::lconstraint_kind::NE, -rational(1));   
            } 
        }
        mk_ineq(m_monomials[i_mon].var(), -rational(sign), not_one_j,lp::lconstraint_kind::EQ);   
        TRACE("nla_solver", print_lemma(tout););
        return true;
    }
    
    bool basic_lemma_for_mon_neutral(unsigned i_mon, const factorization& factorization) {
        return
            basic_lemma_for_mon_neutral_monomial_to_factor(i_mon, factorization) || 
            basic_lemma_for_mon_neutral_from_factors_to_monomial(i_mon, factorization);
        return false;
    }

    
    // use basic multiplication properties to create a lemma
    // for the given monomial
    bool basic_lemma_for_mon(unsigned i_mon) {
        for (auto factorization : factorization_factory_imp(i_mon, *this)) {
            if (factorization.is_empty())
                continue;
            if (basic_lemma_for_mon_zero(i_mon, factorization) ||
                basic_lemma_for_mon_neutral(i_mon, factorization))
                return true;
            
        }
        return false;
    }

    // use basic multiplication properties to create a lemma
    bool basic_lemma(unsigned_vector & to_refine) {
        if (basic_sign_lemma())
            return true;

        for (unsigned i : to_refine) {
            if (basic_lemma_for_mon(i)) {
                return true;
            }
        }
        return false;
    }

    void map_monomial_vars_to_monomial_indices(unsigned i) {
        const monomial& m = m_monomials[i];
        for (lpvar j : m.vars()) {
            auto it = m_monomials_containing_var.find(j);
            if (it == m_monomials_containing_var.end()) {
                unsigned_vector ms;
                ms.push_back(i);
                m_monomials_containing_var[j] = ms;
            }
            else {
                it->second.push_back(i);
            }
        }
    }

    void map_vars_to_monomials() {
        for (unsigned i = 0; i < m_monomials.size(); i++)
            map_monomial_vars_to_monomial_indices(i);
    }

    // we look for octagon constraints here, with a left part  +-x +- y 
    void collect_equivs() {
        const lp::lar_solver& s = m_lar_solver;

        for (unsigned i = 0; i < s.terms().size(); i++) {
            unsigned ti = i + s.terms_start_index();
            if (!s.term_is_used_as_row(ti))
                continue;
            lpvar j = s.external2local(ti);
            if (var_is_fixed_to_zero(j)) {
                TRACE("nla_solver", tout << "term = "; s.print_term(*s.terms()[i], tout););
                add_equivalence_maybe(s.terms()[i], s.get_column_upper_bound_witness(j), s.get_column_lower_bound_witness(j));
            }
        }
    }

    void add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1) {
        if (t->size() != 2)
            return;
        bool seen_minus = false;
        bool seen_plus = false;
        lpvar i = -1, j;
        for(const auto & p : *t) {
            const auto & c = p.coeff();
            if (c == 1) {
                seen_plus = true;
            } else if (c == - 1) {
                seen_minus = true;
            } else {
                return;
            }
            if (i == static_cast<lpvar>(-1))
                i = p.var();
            else
                j = p.var();
        }
        TRACE("nla_solver", tout << "adding equiv";);
        rational sign((seen_minus && seen_plus)? 1 : -1);
        m_vars_equivalence.add_equiv(i, j, sign, c0, c1);
    }

    // x is equivalent to y if x = +- y
    void init_vars_equivalence() {
        m_vars_equivalence.clear();
        collect_equivs();
        m_vars_equivalence.create_tree();
        for (lpvar j = 0; j < m_lar_solver.number_of_vars(); j++) {
            m_vars_equivalence.register_var(j, vvr(j));
        }
    }

    void register_key_mono_in_rooted_monomials(monomial_coeff const& mc, unsigned i) {
        index_with_sign ms(i, mc.coeff());
        auto it = m_rooted_monomials_map.find(mc.vars());
        if (it == m_rooted_monomials_map.end()) {
            vector<index_with_sign> v;
            v.push_back(ms);
            // v is a vector containing a single index_with_sign
            m_rooted_monomials_map.emplace(mc.vars(), v);
        } 
        else {
            it->second.push_back(ms);
        }
    }

    void register_monomial_in_tables(unsigned i) {
        m_vars_equivalence.register_monomial_in_abs_vals(i, m_monomials[i]);
        monomial_coeff mc = canonize_monomial(m_monomials[i]);
        register_key_mono_in_rooted_monomials(mc, i);        
    }

    void fill_vector_of_rooted_monomials() {
        SASSERT(m_vector_of_rooted_monomials.empty());
        for (const auto& p : m_rooted_monomials_map) {
            m_vector_of_rooted_monomials.push_back(p.first);
        }
    }

    void register_rooted_monomial(unsigned i) {
        for (unsigned j : m_vector_of_rooted_monomials[i]) {
            auto it = m_rooted_monomials_containing_var.find(j);
            if (it == m_rooted_monomials_containing_var.end()) {
                std::unordered_set<unsigned> s;
                s.insert(i);
                m_rooted_monomials_containing_var[j] = s;
            } else {
                it->second.insert(i);
            }
        }
    }
    
    void create_rooted_tables() {
        fill_vector_of_rooted_monomials();
        for (unsigned i = 0; i < m_vector_of_rooted_monomials.size(); i++) {
            register_rooted_monomial(i);
        }
    }

    void intersect_set(std::unordered_set<unsigned>& p, const std::unordered_set<unsigned>& w) {
        for (auto it = p.begin(); it != p.end(); ) {
            auto iit = it;
            iit ++;
            if (w.find(*it) == w.end())
                p.erase(it);
            it = iit;
        }
    }

    
    // returns true if a is a factar of b
    bool is_factor(const svector<lpvar> & a, const svector<lpvar> & b) {
        SASSERT(lp::is_non_decreasing(a) && lp::is_non_decreasing(b));
        auto i = a.begin();
        auto j = b.begin();

        while (true) {
            if (i == a.end()) {
                return true;
            }
            if (j == b.end()) {
                return false;
            }

            j = std::lower_bound(j, b.end(), *i);

            if (j == b.end() || *i != *j) {
                return false;
            }
            i++; j++;
        }
        
    }

    void reduce_set_by_checking_actual_containment(std::unordered_set<unsigned>& p,
                                                   const svector<lpvar> & rm ) {
        for (auto it = p.begin(); it != p.end();) {
            if (is_factor(rm, m_vector_of_rooted_monomials[*it])) {
                it++;
                continue;
            }
            auto iit = it;
            iit ++;
            p.erase(it);
            it = iit;
        }
    }
    
    // here i is the index of a monomial in m_vector_of_rooted_monomials
    void find_containing_rooted_monomials(unsigned i) {
        const svector<lpvar> & rm = m_vector_of_rooted_monomials[i];
        std::unordered_set<unsigned> p = m_rooted_monomials_containing_var[rm[0]];
        for (unsigned k = 1; k < rm.size(); k++) {
            intersect_set(p, m_rooted_monomials_containing_var[rm[k]]);
        }
        reduce_set_by_checking_actual_containment(p, rm);
        m_rooted_factor_to_product[i] = p;
    }
    
    void fill_rooted_factor_to_product() {
        for (unsigned i = 0; i < m_vector_of_rooted_monomials.size(); i++) {
            find_containing_rooted_monomials(i);
        }
    }

    void register_monomials_in_tables() {
        m_vars_equivalence.clear_monomials_by_abs_vals();
        for (unsigned i = 0; i < m_monomials.size(); i++) 
            register_monomial_in_tables(i);

        create_rooted_tables();
        fill_rooted_factor_to_product();
    }
    
    void init_search() {
        map_vars_to_monomials();
        init_vars_equivalence();
        register_monomials_in_tables();
        m_expl->clear();
        m_lemma->clear();
    }

    static svector<lpvar> extract_all_but(const svector<lpvar> & vars, unsigned k) {
        static svector<lpvar> ret;
        for (unsigned j = 0; j < vars.size(); j++) {
            if (j == k)
                continue;
            ret.push_back(vars[j]);
        }
        return ret;
    }

    // a > b && c == d => ac > bd
    // ac is a factorization of m_monomials[i_mon]
    // ac[k] plays the role of c
    // d = +-c
    // i_bd_equiv is a candidate for bd
    bool order_lemma_on_factor_equiv_and_other_mon_eq(unsigned b,
                                                      unsigned i_bd_equiv,
                                                      unsigned i_bd,
                                                      unsigned d, unsigned i_ac, const factorization& ac, unsigned k) {
    }
        

    // a > b && c == d => ac > bd
    // ac is a factorization of m_monomials[i_mon]
    // ac[k] plays the role of c
    // d = +-c
    // i_bd_equiv is a candidate for bd
    bool order_lemma_on_factor_equiv_and_other_mon_eq(unsigned i_bd_equiv,
                                                     unsigned i_bd,
                                                     unsigned d, unsigned i_ac, const factorization& ac, unsigned k) {
        TRACE("nla_solver", tout << "i_bd_equiv = "; print_monomial_with_vars(i_bd_equiv, tout); );
        rational abs_d = abs(vvr(d));
        for (unsigned k = 0; k < m_monomials[i_bd_equiv].size(); k++) {
            if (abs(vvr(m_monomials[i_bd_equiv][k])) != abs_d)
                continue;
            svector<lpvar> b = extract_all_but(m_monomials[i_bd_equiv].vars(), k);
            std::sort(b.begin(), b.end());
            auto it = m_rooted_monomials_map.find(b);
            if (it == m_rooted_monomials_map.end())
                return false;
            
            for (const index_with_sign& s : it->second) {
                if (order_lemma_on_factor_equiv_and_other_mon_eq_b(s.var(), i_bd, d, i_bd, d, i_ac, ac, k))
                    return true;
            }
        }
        return false;
    }    

    
    // a > b && c == d => ac > bd
    // ac is a factorization of m_monomials[i_mon]
    // ac[k] plays the role of c
    // d = +-c
    bool order_lemma_on_factor_equiv_and_other_mon(unsigned i_bd, unsigned d, unsigned i_ac, const factorization& ac, unsigned k) {
        if (i_bd == i_ac) {
            return false;
        }

        const monomial & m_bd = m_monomials[i_bd];
        monomial_coeff m_bd_rooted = canonize_monomial(m_bd);
        TRACE("nla_solver", tout << "i_bd monomial = "; print_monomial(m_bd, tout); );
        auto it = m_rooted_monomials_map.find(m_bd_rooted.vars());
        if (it == m_rooted_monomials_map.end())
            return false;
        for (const index_with_sign& s : it->second) {
            if (order_lemma_on_factor_equiv_and_other_mon_eq(s.var(), i_bd, d, i_ac, ac, k))
                return true;
        }
        return false;
    }

    // a > b && c == d => ac > bd
    // ac is a factorization of m_monomials[i_mon]
    // ac[k] plays the role of c
    // d = +-c
    bool order_lemma_on_factor_and_equiv(unsigned d, unsigned i_mon, const factorization& ac, unsigned k) {
        TRACE("nla_solver", tout << "d = " << d << ", k = " << k << ", ac[k] = " << ac[k] << std::endl; );
        SASSERT(abs(vvr(d)) == abs(vvr(ac[k])));
        lpvar j = ac[k];
        for (unsigned i : m_monomials_containing_var[j]) {
            if (order_lemma_on_factor_equiv_and_other_mon(i, d, i_mon, ac, k)) {
                return true;
            }
        }
        return false;
    }

    // a > b && c == d => ac > bd
    // ac is a factorization of m_monomials[i_mon]
    // ac[k] plays the role of c   
    bool order_lemma_on_factor(unsigned i_mon, const factorization& ac, unsigned k) {
        lpvar c = ac[k];
        TRACE("nla_solver", tout << "k = " << k << ", c = " << c; );
        for (const index_with_sign& d : m_vars_equivalence.get_equivalent_vars(c)) {
            TRACE("nla_solver", tout << "d.var() = " << d.var() << ", d.sign() = " << d.sign(); );
            if (order_lemma_on_factor_and_equiv(d.m_i, i_mon, ac, k)) {
                return true;
            }
        }
        return false;
    }

    // a > b && c == d => ac > bd
    // ac is a factorization of m_monomials[i_mon]
    bool order_lemma_on_factorization(unsigned i_mon, const factorization& ac) {
        TRACE("nla_solver", tout << "factorization = "; print_factorization(ac, tout););
        for (unsigned k = 0; k < ac.size(); k++) {
            const rational & v = vvr(ac[k]);
            if (v.is_zero())
                continue;

            if (order_lemma_on_factor(i_mon, ac, k)) { 
                return true;
            }
        }
        return false;
    }

     // a > b && c == d => ac > bd
    bool order_lemma_on_monomial(unsigned i_mon) {
        TRACE("nla_solver", print_monomial_with_vars(i_mon, tout););
        for (auto ac : factorization_factory_imp(i_mon, *this)) {
            if (ac.is_empty())
                continue;
            if (order_lemma_on_factorization(i_mon, ac))
                return true;
        }
        return false;
    }
    
    bool order_lemma(const unsigned_vector& to_refine) {
        for (unsigned i_mon : to_refine) {
            if (order_lemma_on_monomial(i_mon)) {
                return true;
            } 
        }
        return false;
    }

    bool monotonicity_lemma_on_factorization(unsigned i_mon, const factorization& factorization) {
        return false;
    }
    
    bool monotonicity_lemma_on_monomial(unsigned i_mon) {
        for (auto factorization : factorization_factory_imp(i_mon, *this)) {
            if (factorization.is_empty())
                continue;
            if (monotonicity_lemma_on_factorization(i_mon, factorization))
                return true;
        }
        return false;
    }
    
    bool monotonicity_lemma(const unsigned_vector& to_refine) {
        for (unsigned i_mon : to_refine) {
            if (monotonicity_lemma_on_monomial(i_mon)) {
                return true;
            } 
        }
        
        return false;
    }

    bool tangent_lemma(const unsigned_vector& to_refine) {
        return false;
    }
    
    lbool check(lp::explanation & exp, lemma& l) {
        TRACE("nla_solver", tout << "check of nla";);
        m_expl =   &exp;
        m_lemma =  &l;
       
        if (!(m_lar_solver.get_status() == lp::lp_status::OPTIMAL || m_lar_solver.get_status() == lp::lp_status::FEASIBLE )) {
            TRACE("nla_solver", tout << "unknown because of the m_lar_solver.m_status = " << lp_status_to_string(m_lar_solver.get_status()) << "\n";);
            return l_undef;
        }

        unsigned_vector to_refine;
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            if (!check_monomial(m_monomials[i]))
                to_refine.push_back(i);
        }

        if (to_refine.empty()) {
            return l_true;
        }

        TRACE("nla_solver", tout << "to_refine.size() = " << to_refine.size() << std::endl;);
        
        init_search();
        for (int search_level = 0; search_level < 3; search_level++) {
            if (search_level == 0) {
                if (basic_lemma(to_refine)) {
                    return l_false;
                }
            } else if (search_level == 1) {
                if (order_lemma(to_refine)) {
                    return l_false;
                }
            } else { // search_level == 3
                if (monotonicity_lemma(to_refine)) {
                    return l_false;
                }
                                
                if (tangent_lemma(to_refine)) {
                    return l_false;
                }
            }
    }
    
    return l_undef;
}
    
    void test_factorization(unsigned mon_index, unsigned number_of_factorizations) {
        vector<ineq> lemma;
        m_lemma = & lemma;
        lp::explanation exp;
        m_expl = & exp;
        init_search();

        factorization_factory_imp fc(mon_index, // 0 is the index of "abcde"
                                             *this);
     
        std::cout << "factorizations = of "; print_var(m_monomials[0].var(), std::cout) << "\n";
        unsigned found_factorizations = 0;
        for (auto f : fc) {
            if (f.is_empty()) continue;
            found_factorizations ++;
            for (lpvar j : f) {
                std::cout << "j = "; print_var(j, std::cout);
            }
            std::cout << "sign = " << f.sign() << std::endl;
        }
        SASSERT(found_factorizations == number_of_factorizations);
    }
    
    lbool test_check(
        vector<ineq>& lemma,
        lp::explanation& exp )
    {
        m_lar_solver.set_status(lp::lp_status::OPTIMAL);
        m_lemma = & lemma;
        m_expl = & exp;

        return check(exp, lemma);
    }
}; // end of imp



void solver::add_monomial(lpvar v, unsigned sz, lpvar const* vs) {
    m_imp->add(v, sz, vs);
}

bool solver::need_check() { return true; }

lbool solver::check(lp::explanation & ex, lemma& l) {
    return m_imp->check(ex, l);
}

void solver::push(){
    m_imp->push();
}

void solver::pop(unsigned n) {
    m_imp->pop(n);
}
        
solver::solver(lp::lar_solver& s, reslimit& lim, params_ref const& p) {
    m_imp = alloc(imp, s, lim, p);
}

solver::~solver() {
    dealloc(m_imp);
}

void create_abcde(solver & nla,
                  unsigned lp_a,
                  unsigned lp_b,
                  unsigned lp_c,
                  unsigned lp_d,
                  unsigned lp_e,
                  unsigned lp_abcde,
                  unsigned lp_ac,
                  unsigned lp_bde,
                  unsigned lp_acd,
                  unsigned lp_be) {
    // create monomial abcde
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    vec.push_back(lp_e);

    nla.add_monomial(lp_abcde, vec.size(), vec.begin());

    // create monomial ac
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    nla.add_monomial(lp_ac, vec.size(), vec.begin());

    // create monomial bde
    vec.clear();
    vec.push_back(lp_b);
    vec.push_back(lp_d);
    vec.push_back(lp_e);
    nla.add_monomial(lp_bde, vec.size(), vec.begin());

    // create monomial acd
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monomial(lp_acd, vec.size(), vec.begin());

    // create monomial be
    vec.clear();
    vec.push_back(lp_b);
    vec.push_back(lp_e);
    nla.add_monomial(lp_be, vec.size(), vec.begin());
}

void solver::test_factorization() {
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);

    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);

    nla.m_imp->test_factorization(0, // 0 is the index of monomial abcde
                                  3); // 3 is the number of expected factorizations

    
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial() {
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0();
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1();
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0\n";
    // enable_trace("nla_solver");
    TRACE("nla_solver",);
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    svector<lpvar> v; v.push_back(lp_b);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monomial(lp_bde, v.size(), v.begin());
    v.clear();
    v.push_back(lp_a);v.push_back(lp_b);v.push_back(lp_c);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monomial(lp_abcde, v.size(), v.begin());
    v.clear();
    v.push_back(lp_a);v.push_back(lp_c);
    nla.add_monomial(lp_ac, v.size(), v.begin());
     
    vector<ineq> lemma;
    lp::explanation exp;

    // set abcde = ac * bde
    // ac = 1, bde = 3 -> abcde = bde, but we have abcde set to 2
    s.set_column_value(lp_a, rational(4));
    s.set_column_value(lp_b, rational(4));
    s.set_column_value(lp_c, rational(4));
    s.set_column_value(lp_d, rational(4));
    s.set_column_value(lp_e, rational(4));
    s.set_column_value(lp_abcde, rational(2));
    s.set_column_value(lp_ac, rational(1));
    s.set_column_value(lp_bde, rational(3));

    
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");

    ineq i0(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i0.m_term.add_coeff_var(lp_ac);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_coeff_var(lp_bde);
    i1.m_term.add_coeff_var(-rational(1), lp_abcde);
    ineq i2(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_coeff_var(lp_abcde);
    i2.m_term.add_coeff_var(-rational(1), lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    for (const auto& k : lemma){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2) {
            found2 = true;
        } 
    }

    SASSERT(found0 && (found1 || found2));

    
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1\n";
    TRACE("nla_solver",);
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
         bde = 7;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_bde = s.add_var(bde, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    svector<lpvar> v; v.push_back(lp_b);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monomial(lp_bde, v.size(), v.begin());

    vector<ineq> lemma;
    lp::explanation exp;

    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_b, rational(1));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));
    s.set_column_value(lp_bde, rational(3));

    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    SASSERT(lemma.size() == 4);
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");

    ineq i0(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i1.m_term.add_coeff_var(lp_d);
    ineq i2(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i2.m_term.add_coeff_var(lp_e);
    ineq i3(lp::lconstraint_kind::EQ, lp::lar_term(), rational(1));
    i3.m_term.add_coeff_var(lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    bool found3 = false;
    for (const auto& k : lemma){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2) {
            found2 = true;
        } else if (k == i3) {
            found3 = true;
        }

    }

    SASSERT(found0 && found1 && found2 && found3);

}

void solver::test_basic_lemma_for_mon_zero_from_factors_to_monomial() {
    std::cout << "test_basic_lemma_for_mon_zero_from_factors_to_monomial\n";
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    vector<ineq> lemma;
    lp::explanation exp;


    // set vars
    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_b, rational(0));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));
    s.set_column_value(lp_abcde, rational(0));
    s.set_column_value(lp_ac, rational(1));
    s.set_column_value(lp_bde, rational(0));
    s.set_column_value(lp_acd, rational(1));
    s.set_column_value(lp_be, rational(1));

    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");
    SASSERT(lemma.size() == 2);
    ineq i0(lp::lconstraint_kind::NE, lp::lar_term(), rational(0));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_coeff_var(lp_be);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        }
    }

    SASSERT(found0 && found1);
}

void solver::test_basic_lemma_for_mon_zero_from_monomial_to_factors() {
    std::cout << "test_basic_lemma_for_mon_zero_from_monomial_to_factors\n";
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    vector<ineq> lemma;
    lp::explanation exp;


    s.set_column_value(lp_b, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));

    // set bde to zero
    s.set_column_value(lp_bde, rational(0));

    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");

    ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_coeff_var(lp_d);
    ineq i2(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_coeff_var(lp_e);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;

    for (const auto& k : lemma){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2){
            found2 = true;
        }
    }

    SASSERT(found0 && found1 && found2);
    
}

void solver::test_basic_lemma_for_mon_neutral_from_monomial_to_factors() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_monomial_to_factors\n";
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    vector<ineq> lemma;
    lp::explanation exp;

    // set all vars to 1
    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_b, rational(1));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));
    s.set_column_value(lp_abcde, rational(1));
    s.set_column_value(lp_ac, rational(1));
    s.set_column_value(lp_bde, rational(1));
    s.set_column_value(lp_acd, rational(1));
    s.set_column_value(lp_be, rational(1));

    // set bde to 2, b to minus 2
    s.set_column_value(lp_bde, rational(2));
    s.set_column_value(lp_b, - rational(2));
    // we have bde = -b, therefore d = +-1 and e = +-1
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");
    ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(1));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), -rational(1));
    i1.m_term.add_coeff_var(lp_b);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        }
    }

    SASSERT(found0 && found1);
}

void solver::test_basic_sign_lemma() {
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        bde = 7, acd = 8;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial abcde
    vector<unsigned> vec;

    vec.push_back(lp_b);
    vec.push_back(lp_d);
    vec.push_back(lp_e);

    nla.add_monomial(lp_bde, vec.size(), vec.begin());
    vec.clear();

    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);

    nla.add_monomial(lp_acd, vec.size(), vec.begin());

    // make the products bde = -acd according to the model
    
    // b = -a
    s.set_column_value(lp_a, rational(7));
    s.set_column_value(lp_b, rational(-7));
    
    // e - c = 0
    s.set_column_value(lp_e, rational(4));
    s.set_column_value(lp_c, rational(4));

    s.set_column_value(lp_d, rational(6));

    //    make bde != -acd according to the model
    s.set_column_value(lp_bde, lp::impq(rational(5)));
    s.set_column_value(lp_acd, lp::impq(rational(3)));
   
    vector<ineq> lemma;
    lp::explanation exp;
    
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);

    lp::lar_term t;
    t.add_coeff_var(lp_bde);
    t.add_coeff_var(lp_acd);
    ineq q(lp::lconstraint_kind::EQ, t, rational(0));
   
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");
    SASSERT(q == lemma.back());
    ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i0.m_term.add_coeff_var(lp_bde);
    i0.m_term.add_coeff_var(rational(1), lp_acd);
    bool found = false;
    for (const auto& k : lemma){
        if (k == i0) {
            found = true;
        } 
    }

    SASSERT(found);
}

void solver::test_order_lemma() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4, f = 5, 
        i = 8, j = 9,
        ab = 10, cd = 11, ef = 12, abef = 13, cdij = 16, ij = 17;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_f = s.add_named_var(f, true, "f");
    lpvar lp_i = s.add_named_var(i, true, "i");
    lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    lpvar lp_cd = s.add_named_var(cd, true, "cd");
    lpvar lp_ef = s.add_named_var(ef, true, "ef");
    lpvar lp_ij = s.add_named_var(ij, true, "ij");
    lpvar lp_abef = s.add_named_var(abef, true, "abef");
    lpvar lp_cdij = s.add_named_var(cdij, true, "cdij");

    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        s.set_column_value(j, rational(3));
    }
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    nla.add_monomial(lp_ab, vec.size(), vec.begin());
    // create monomial cd
    vec.clear();
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monomial(lp_cd, vec.size(), vec.begin());
    // create monomial ef
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_f);
    nla.add_monomial(lp_ef, vec.size(), vec.begin());
    // create monomial ij
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    nla.add_monomial(lp_ij, vec.size(), vec.begin());
    
    // make ab < cd it the model
    s.set_column_value(lp_ab, rational(7));
    s.set_column_value(lp_cd, rational(8));

    s.set_column_value(lp_a,  rational(4));
    s.set_column_value(lp_b,  rational(4));
    s.set_column_value(lp_c,  rational(2));
    s.set_column_value(lp_d,  rational(3));
    //create monomial abef 
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    vec.push_back(lp_f);
    nla.add_monomial(lp_abef, vec.size(), vec.begin());

    s.set_column_value(lp_e,  rational(9));
    s.set_column_value(lp_f,  rational(11));

    //create monomial cdij
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monomial(lp_cdij, vec.size(), vec.begin());

    // set ij == ef in the model
    s.set_column_value(lp_ij, rational(17));
    s.set_column_value(lp_ef, rational(17));

    // set abef = cdij, while it has to be abef < cdij
    s.set_column_value(lp_abef, rational(18));
    s.set_column_value(lp_cdij, rational(18));
   
    vector<ineq> lemma;
    lp::explanation exp;
    
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);

    // lp::lar_term t;
    // t.add_coeff_var(lp_bde);
    // t.add_coeff_var(lp_acd);
    // ineq q(lp::lconstraint_kind::EQ, t, rational(0));
   
    nla.m_imp->print_lemma(std::cout << "lemma: ");
    // SASSERT(q == lemma.back());
    // ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    // i0.m_term.add_coeff_var(lp_bde);
    // i0.m_term.add_coeff_var(rational(1), lp_acd);
    // bool found = false;
    // for (const auto& k : lemma){
    //     if (k == i0) {
    //         found = true;
    //     } 
    // }

    // SASSERT(found);
}
}
