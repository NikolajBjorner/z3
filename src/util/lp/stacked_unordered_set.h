/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#ifdef LEAN_DEBUG
#pragma once
// this class implements an unordered_set with some stack functionality
#include <unordered_set>
#include <set>
#include <stack>
namespace lean {

template <typename A, 
          typename Hash = std::hash<A>,
          typename KeyEqual = std::equal_to<A>,
          typename Allocator = std::allocator<A>
          > class stacked_unordered_set {
    struct delta {
        std::unordered_set<A, Hash, KeyEqual> m_new;
    };
    std::unordered_set<A, Hash, KeyEqual, Allocator> m_set;
    std::stack<delta> m_stack;
public:
    void insert(const A & a) {
        if (m_stack.empty()) {
            m_set.insert(a);
        } else {
            if (m_set.find(a) == m_set.end()) {
                m_stack.top().m_new.insert(a);
                m_set.insert(a);
            }
        }
    }
    
    
    unsigned size() const {
        return m_set.size();
    }

    bool contains(A & key) const {
        return m_set.find(key) != m_set.end();
    }

    bool contains(A && key) const {
        return m_set.find(std::move(key)) != m_set.end();
    }
    
    void push() {
        delta d;
        m_stack.push(d);
    }
    
    void pop() {
        pop(1);
    }
    void pop(unsigned k) {
        while (k-- > 0) {
            if (m_stack.empty())
                return;
            delta & d = m_stack.top();
            for (auto & t : d.m_new) {
                m_set.erase(t);
            }
            m_stack.pop();
        }
    }

    const std::unordered_set<A, Hash, KeyEqual, Allocator>& operator()() const { return m_set;}
};
}
#endif
