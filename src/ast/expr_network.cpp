/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    expr_network.cpp

Abstract:

    expr network.

Author:

    Nikolaj Bjorner (nbjorner) 6-14-2019

Revision History:

--*/

#include "ast/expr_network.h"

void expr_network::add_root(expr* e) {
    m_roots.push_back(e);
    svector<std::pair<expr*,expr*>> todo;
    todo.push_back(std::make_pair(e, nullptr));
    for (unsigned i = 0; i < todo.size(); ++i) {
        expr* e = todo[i].first;
        expr* p = todo[i].second;
        unsigned id = e->get_id();
        while (id >= m_nodes.size()) {
            m_nodes.push_back(node(expr_ref(m)));
        }
        node& n = m_nodes[id];
        if (p) {
            n.m_parents.push_back(p->get_id());
        }
        if (!n.m_expr) {
            n.m_expr = e;
            if (is_app(e)) {
                for (expr* arg : *to_app(e)) {
                    n.m_children.push_back(arg->get_id());
                    todo.push_back(std::make_pair(arg, e));
                }
            }
        }
    }
}

expr_ref_vector expr_network::get_roots() {
    unsigned_vector todo;
    for (expr* r : m_roots) {
        todo.push_back(r->get_id());
    }
    expr_ref_vector node2expr(m);
    svector<bool> valid;
    ptr_vector<expr> args;
    valid.reserve(m_nodes.size(), false);
    for (auto const& n : m_nodes) {
        node2expr.push_back(n.m_expr);
    }
    while (!todo.empty()) {
        unsigned id = todo.back();
        if (valid[id]) {            
            todo.pop_back();
            continue;
        }
        bool all_valid = true;
        args.reset();
        for (unsigned child : m_nodes[id].m_children) {
            if (!valid[child]) {
                todo.push_back(child);
                all_valid = false;
            }
            else if (all_valid) {
                args.push_back(node2expr.get(child));
            }
        }
        if (all_valid) {
            expr* e = m_nodes[id].e();
            if (is_app(e)) {
                func_decl* f = to_app(e)->get_decl();
                node2expr[id] = m.mk_app(f, args.size(), args.c_ptr());
            }
            else {
                node2expr[id] = e;
            }
            valid[id] = true;
            todo.pop_back();
        }
    }
    expr_ref_vector result(m);
    for (expr* r : m_roots) {
        result.push_back(node2expr.get(r->get_id()));
    }
    return result;
}

void expr_network::substitute(unsigned src, unsigned dst) {
    if (src == dst) {
        return;
    }
    for (unsigned parent : m_nodes[src].m_parents) {
        for (unsigned& ch : m_nodes[parent].m_children) {
            if (ch == src) {
                ch = dst;
            }
        }
    }
    m_nodes[src].m_parents.reset();
}

unsigned_vector expr_network::top_sort() {
    unsigned_vector result;
    svector<bool> visit;
    visit.reserve(m_nodes.size(), false);
    unsigned_vector todo;
    for (node const& n : m_nodes) {
        if (n.e()) todo.push_back(n.id());
    }
    while (!todo.empty()) {
        unsigned id = todo.back();
        if (visit[id]) {
            todo.pop_back();
            continue;
        }
        bool all_visit = true;
        for (unsigned child : m_nodes[id].m_children) {
            if (!visit[child]) {
                todo.push_back(child);
                all_visit = false;
            }
        }
        if (all_visit) {
            visit[id] = true;
            result.push_back(id);
            todo.pop_back();
        }
    }
    return result;
}

vector<expr_network::cut_set> expr_network::get_cuts(unsigned k) {
    unsigned_vector sorted = top_sort();
    vector<cut_set> cuts;
    cuts.resize(m_nodes.size());
    svector<cut> cut_set2;
    for (unsigned id : sorted) {
        auto& cut_set = cuts[id];
        SASSERT(cut_set.empty());
        node const& n = m_nodes[id];
        if (is_ite(n)) {
            for (auto const& a : cuts[n.m_children[0]]) {
                for (auto const& b : cuts[n.m_children[1]]) {
                    cut ab;
                    if (!ab.merge(a, b)) {
                        continue;
                    }
                    for (auto const& c : cuts[n.m_children[2]]) {
                        cut abc;
                        if (!abc.merge(ab, c)) {
                            continue;
                        }
                        uint64_t t1 = a.shift_table(abc);
                        uint64_t t2 = b.shift_table(abc);
                        uint64_t t3 = c.shift_table(abc);
                        abc.m_table = (t1 & t2) | (~t1 & t3);
                        cut_set.insert(abc);
                    } 
                }
            }
        }
        else if (is_not(n)) {
            for (auto const& a : cuts[n.m_children[0]]) {
                cut_set.push_back(a);
                cut_set.back().m_table = ~a.m_table;
            }
        }
        else if ((is_ac_bool_op(n)) && n.m_children.size() < k) {
            bool first = true;
            for (unsigned child : n.m_children) {
                if (first) {
                    for (auto const& a : cuts[child]) {
                        cut_set.push_back(a);
                    }
                    first = false;
                    continue;
                }
                cut_set2.reset();
                for (auto const& a : cut_set) {
                    for (auto const& b : cuts[child]) {
                        cut c;
                        if (c.merge(a, b)) {
                            uint64_t t1 = a.shift_table(c);
                            uint64_t t2 = b.shift_table(c);
                            switch (get_decl_kind(n)) {
                            case OP_AND: c.m_table = t1 & t2; break;
                            case OP_OR:  c.m_table = t1 | t2; break;
                            case OP_XOR: c.m_table = t1 ^ t2; break;
                            case OP_EQ:  c.m_table = ~(t1 ^ t2); break;
                            default: UNREACHABLE(); break;
                            }
                            cut_set2.insert(c);
                        }
                    }
                }
                cut_set.swap(cut_set2);
            }
        }
        cut_set.push_back(cut(id));
    }
    return cuts;
}

bool expr_network::is_not(node const& n) const {
    return n.e() && m.is_not(n.e());
}

bool expr_network::is_ac_bool_op(node const& n) const {
    return n.e() && (m.is_and(n.e()) || m.is_or(n.e()) || m.is_iff(n.e()) || m.is_xor(n.e()));
}

bool expr_network::is_ite(node const& n) const {
    return n.e() && m.is_ite(n.e()) && m.is_bool(to_app(n.e())->get_arg(1));
}

decl_kind expr_network::get_decl_kind(node const& n) const {
    return to_app(n.e())->get_decl_kind();
}


/**
   \brief
   if c is subsumed by a member in cut_set, then c is not inserted.
   otherwise, remove members that c subsumes.
   Note that the cut_set maintains invariant that elements don't subsume each-other.
 */

void expr_network::cut_set::insert(cut const& c) {
    unsigned i = 0, j = 0;
    for (; i < size(); ++i) {
        cut const& a = (*this)[i];
        if (a.subset_of(c)) {
            return;
        }
        if (c.subset_of(a)) {
            continue;
        }
        else if (j < i) {
            (*this)[j] = a;
        }
        ++j;
    }
    if (j < i) {
        shrink(j);
    }
}

uint64_t expr_network::cut::shift_table(cut const& c) const {
    return 0;
}
