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
    svector<cut> cut_set, new_cutset;
    for (unsigned id : sorted) {
        auto& cut_set = cuts[id];
        SASSERT(cut_set.empty());
        node const& n = m_nodes[id];
        if (n.m_children.size() < k && is_bool_op(n.e())) {
            for (unsigned i = 0, sz = n.m_children.size(); i < sz; ++i) {
                unsigned child = n.m_children[i];
                if (i == 0) {
                    unsigned j = 0;
                    for (auto const& a : cuts[child]) {
                        cut_set.push_back(a);
                        cut_set.back().m_table = j++;
                    }
                    continue;
                }
                new_cutset.reset();
                for (auto const& a : cut_set) {
                    for (unsigned j = 0, csz = cuts[child].size(); j < csz; ++j) {
                        auto const& b = cuts[child][j];
                        cut c;
                        if (c.merge(a, b)) {
                            // remember index of child
                            c.m_table = a.m_table;
                            c.m_table |= j << (i << 3);
                            new_cutset.insert(c);
                        }
                    }
                }
                // effect on value in cuts[id]?
                cut_set.swap(new_cutset); 
            }

            // TBD: compute truth tables:
            uint64_t rs[3];
            switch (to_app(n.e())->get_decl_kind()) {
            case OP_AND:
                for (cut& c : cut_set) {
                    uint64_t r = ~((uint64_t)(0));
                    for (unsigned i = 0, sz = n.m_children.size(); i < sz; ++i) {
                        r &= cuts[n.m_children[i]][(c.m_table >> (i << 3)) & 0xFF].shift_table(c);
                    }
                    c.m_table = r;
                }
                break;
            case OP_OR:
                for (cut& c : cut_set) {
                    uint64_t r = ~((uint64_t)(0));
                    for (unsigned i = 0, sz = n.m_children.size(); i < sz; ++i) {
                        r |= cuts[n.m_children[i]][(c.m_table >> (i << 3)) & 0xFF].shift_table(c);
                    }
                    c.m_table = r;
                }
                break;
            case OP_NOT:
                for (cut& c : cut_set) {
                    c.m_table = ~(cuts[n.m_children[0]][c.m_table].shift_table(c));
                }
                break;
            case OP_EQ:
                for (cut& c : cut_set) {
                    uint64_t r = ~((uint64_t)(0));
                    for (unsigned i = 0, sz = n.m_children.size(); i < sz; ++i) {
                        r = ~ (r ^ cuts[n.m_children[i]][(c.m_table >> (i << 3)) & 0xFF].shift_table(c));
                    }
                    c.m_table = r;
                }
                break;
            case OP_TRUE:
                for (cut& c : cut_set) {
                    c.m_table = ~((uint64_t)(0));
                }
                break;
            case OP_FALSE:
                for (cut& c : cut_set) {
                    c.m_table = 0;
                }
                break;
            case OP_ITE:
                for (cut& c : cut_set) {
                    for (unsigned i = 0; i < 3; ++i) {
                        rs[i] = cuts[n.m_children[i]][(c.m_table >> (i << 3)) & 0xFF].shift_table(c);
                    }
                    c.m_table = (rs[0] & rs[1]) | (~rs[0] & rs[2]);
                }
                break;
            default:
                UNREACHABLE();
            }

        }
        cut_set.push_back(cut(id));
    }
    return cuts;
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
