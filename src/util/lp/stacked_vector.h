/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Lev Nachmanson
*/
#pragma once
#include <unordered_map>
#include <set>
#include <stack>
#include <vector>
namespace lean {
template < typename B> class stacked_vector {
    struct delta {
        unsigned m_size;
        std::unordered_map<unsigned, B> m_original_changed;
        //        std::vector<B> m_deb_copy;
    };
    std::vector<B> m_vector;
    std::stack<delta> m_stack;
public:
    class ref {
        stacked_vector<B> & m_vec;
        unsigned m_i;
    public:
        ref(stacked_vector<B> &m, unsigned key) :m_vec(m), m_i(key) {
            lean_assert(key < m.size());
        }
        ref & operator=(const B & b) {
            m_vec.emplace_replace(m_i, b);
            return *this;
        }
        ref & operator=(const ref & b) { lean_assert(false); return *this; }
        operator const B&() const {
            return m_vec.m_vector[m_i];
        }
    };
private:
    void emplace_replace(unsigned i,const B & b) {
        if (!m_stack.empty()) {
            if (m_vector[i] == b)
                return;
            delta & d = m_stack.top();
            if (i < d.m_size) {
                auto & orig_changed = d.m_original_changed;
                auto it = orig_changed.find(i);
                if (it == orig_changed.end())
                    orig_changed.emplace(i, m_vector[i] );
                else if (it->second == b)
                    orig_changed.erase(it);
            }
        }
        m_vector[i] = b;
    }
public:
    ref operator[] (unsigned a) {
        return ref(*this, a);
    }

    const B & operator[](unsigned a) const {
        lean_assert(a < m_vector.size());
        return m_vector[a];
    }

    
    unsigned size() const {
        return m_vector.size();
    }

    
    void push() {
        delta d;
        d.m_size = m_vector.size();
        //        d.m_deb_copy = m_vector;
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
            lean_assert(m_vector.size() >= d.m_size);
            while (m_vector.size() > d.m_size)
                m_vector.pop_back();
            
            for (auto & t : d.m_original_changed) {
                lean_assert(t.first < m_vector.size());
                m_vector[t.first] = t.second;
            }
            //            lean_assert(d.m_deb_copy == m_vector);
            m_stack.pop();
        }
    }

    void clear() {
        if (m_stack.empty()) {
            m_vector.clear();
            return;
        }

        delta & d = m_stack.top();
        auto & oc = d.m_original_changed;
        for (auto & p : m_vector) {
            const auto & it = oc.find(p.first);
            if (it == oc.end() && d.m_new.find(p.first) == d.m_new.end())
                oc.emplace(p.first, p.second);
        }
        m_vector.clear();
    }

    void push_back(const B & b)
    {
        m_vector.push_back(b);
    }

    const std::vector<B>& operator()() const { return m_vector; }
};
}

