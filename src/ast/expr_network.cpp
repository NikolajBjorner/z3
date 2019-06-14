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

vector<svector<expr_network::cut>> expr_network::get_cuts(unsigned k) {
    unsigned_vector sorted = top_sort();
    vector<svector<cut>> cuts;
    cuts.resize(m_nodes.size());
    svector<cut> cut_set, new_cutset;
    for (unsigned id : sorted) {
        svector<cut>& cut_set = cuts[id];
        SASSERT(cut_set.empty());
        node const& n = m_nodes[id];
        if (n.m_children.size() < k) {
            bool first = true;
            for (unsigned child : n.m_children) {
                if (first) {
                    cut_set.append(cuts[child]);
                    first = false;
                    continue;
                }
                new_cutset.reset();
                for (auto const& a : cut_set) {
                    for (auto const& b : cuts[child]) {
                        cut c;
                        if (c.merge(a, b)) {
                            new_cutset.push_back(c);
                        }
                    }
                }
                
                // effect on value in cuts[id]?
                cut_set.swap(new_cutset); 

                // TBD: pruning
            }
        }
        cut_set.push_back(cut(id));
    }
    return cuts;
}

