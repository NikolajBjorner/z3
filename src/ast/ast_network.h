/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    ast_network.h

Abstract:

    View of expressions ast a network.
    The network view offers access to parents (use-lists)
    and supports functions to change nodes.

Author:

    Nikolaj Bjorner (nbjorner) 6-14-2019

Revision History:

--*/
#ifndef AST_NETWORK_H_
#define AST_NETWORK_H_

#include "ast/ast.h"

class ast_network {
public:
    class node {
        friend class ast_network;
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
private:
    ast_manager& m;
    expr_ref_vector m_roots;
    vector<node>    m_nodes;

public:
    ast_network(ast_manager& m): m(m), m_roots(m) {}
    void add_root(expr* e);
    expr_ref_vector get_roots();

    vector<node> const& nodes() { return m_nodes; }
    void substitute(unsigned src, unsigned dst);
};


#endif /* AST_NETWORK_H_ */
