/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    expr_network.h

Abstract:

    View of expressions ast a network.
    The network view offers access to parents (use-lists)
    and supports functions to change nodes.

Author:

    Nikolaj Bjorner (nbjorner) 6-14-2019

Revision History:

--*/
#ifndef EXPR_NETWORK_H_
#define EXPR_NETWORK_H_

#include "ast/ast.h"

class expr_network {
public:
    class node {
        friend class expr_network;
        expr_ref        m_expr;
    public:
        unsigned_vector m_children;
        unsigned_vector m_parents;
        unsigned        m_value{0};
        unsigned        m_visited{0};
        
        node(expr_ref & e):m_expr(e) {}
        node(node& n): 
            m_expr(n.m_expr), 
            m_children(n.m_children), 
            m_parents(n.m_parents), 
            m_value(n.m_value), 
            m_visited(n.m_visited) {}

        unsigned id() const { return m_expr->get_id(); }
        expr* e() const { return m_expr; }
    };

    static const unsigned max_size = 6;

    struct cut {
        unsigned m_size;
        unsigned m_elems[max_size];
        cut(): m_size(0) {}

        cut(unsigned id): m_size(1) { m_elems[0] = id; }

        bool add(unsigned i) {
            if (m_size >= max_size) {
                return false;
            }
            else {
                m_elems[m_size++] = i;
                return true;
            }
        }

        unsigned get(unsigned idx) const {
            return (idx >= m_size) ? UINT_MAX : m_elems[idx];
        }

        bool merge(cut const& a, cut const& b) {
            SASSERT(a.m_size > 0 && b.m_size > 0);
            unsigned i = 0, j = 0;
            unsigned x = a.m_elems[i];
            unsigned y = b.m_elems[j];
            while (x != UINT_MAX && y != UINT_MAX) {
                if (x < y) {
                    if (!add(x)) return false;
                    x = a.get(++i);
                }
                else if (y < x) {
                    if (!add(y)) return false;
                    y = b.get(++j);
                }
                else {
                    if (!add(x)) return false;
                    x = a.get(++i);
                    y = b.get(++j);
                }
            }
            return true;
        }
    };

private:
    ast_manager& m;
    expr_ref_vector m_roots;
    vector<node>    m_nodes;

public:
    expr_network(ast_manager& m): m(m), m_roots(m) {}
    void add_root(expr* e);
    expr_ref_vector get_roots();

    vector<node> const& nodes() { return m_nodes; }
    unsigned_vector top_sort();
    void substitute(unsigned src, unsigned dst);
    vector<svector<cut>> get_cuts(unsigned k);
};


#endif /* EXPR_NETWORK_H_ */
