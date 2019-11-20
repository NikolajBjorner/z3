/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    expr_network.h

Abstract:

    View of expressions ast a network.
    The network view offers access to parents (use-lists)
    and supports functions to change nodes.


Plan for reconvergency driven cuts:
1. given selection of root (outside of this procedure)
2. traverse children as long as cost function is managed (good to revisit children already seen).
3. sat sweeping
4. MFFC on collisions:
   recomputes reference counts based on internal reachability.
   choose node with largest 0-ref subgraph.

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
        unsigned m_filter;
        unsigned m_size;
        unsigned m_elems[max_size];
        uint64_t m_table;
        cut(): m_filter(0), m_size(0), m_table(0) {}

        cut(unsigned id): m_filter(1u << (id & 0x1F)), m_size(1), m_table(2) { m_elems[0] = id; }

        unsigned const* begin() const { return m_elems; }
        unsigned const* end() const  { return m_elems + m_size; }

        bool add(unsigned i) {
            if (m_size >= max_size) {
                return false;
            }
            else {
                m_elems[m_size++] = i;
                m_filter |= (1u << (i & 0x1F));
                return true;
            }
        }
        void sort();

        bool operator==(cut const& other) const;
        unsigned hash() const;
        struct eq_proc { 
            bool operator()(cut const& a, cut const& b) const { return a == b; }
            bool operator()(cut const* a, cut const* b) const { return *a == *b; }
        };
        struct hash_proc {
            unsigned operator()(cut const& a) const { return a.hash(); }
            unsigned operator()(cut const* a) const { return a->hash(); }
        };

        unsigned operator[](unsigned idx) const {
            return (idx >= m_size) ? UINT_MAX : m_elems[idx];
        }

        uint64_t shift_table(cut const& other) const;

        bool merge(cut const& a, cut const& b) {
            SASSERT(a.m_size > 0 && b.m_size > 0);
            unsigned i = 0, j = 0;
            unsigned x = a[i];
            unsigned y = b[j];
            while (x != UINT_MAX || y != UINT_MAX) {
                if (!add(std::min(x, y))) {
                    return false;
                }
                if (x < y) {
                    x = a[++i];
                }
                else if (y < x) {
                    y = b[++j];
                }
                else {
                    x = a[++i];
                    y = b[++j];
                }
            }
            return true;
        }

        bool subset_of(cut const& other) const {
            if (other.m_filter != (m_filter | other.m_filter)) {
                return false;
            }
            unsigned i = 0;
            unsigned other_id = other[i];
            for (unsigned id : *this) {
                while (id > other_id) {
                    other_id = other[++i];
                }
                if (id != other_id) return false;
                other_id = other[++i];
            }
            return true;
        }

        std::ostream& display(std::ostream& out) const;
    };

    struct cut_set : public svector<cut> {
        void insert(cut const& c);
        bool no_duplicates() const;
    };

private:
    ast_manager& m;
    expr_ref_vector m_roots;
    vector<node>    m_nodes;

    bool is_not(node const&) const;
    bool is_ac_bool_op(node const&) const;
    bool is_ite(node const&) const;
    decl_kind get_decl_kind(node const&) const;

public:
    expr_network(ast_manager& m): m(m), m_roots(m) {}
    void add_root(expr* e);
    expr_ref_vector get_roots();

    vector<node> const& nodes() { return m_nodes; }
    unsigned_vector top_sort();
    void substitute(unsigned src, unsigned dst);
    vector<cut_set> get_cuts(unsigned max_cut_size, unsigned max_cutset_size);
    unsigned depth(unsigned id) const;
};

inline std::ostream& operator<<(std::ostream& out, expr_network::cut const& cut) {
    return cut.display(out);
}

#endif /* EXPR_NETWORK_H_ */
