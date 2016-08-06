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
		//        std::unordered_map<A,B, Hash, KeyEqual, Allocator > m_deb_copy;
	};
	std::vector<B> m_vector;
	std::stack<delta> m_stack;
public:
	// class ref {
	// 	stacked_vector<B> & m_vec;
	// 	unsigned m_i;
	// public:
 	// 	ref(stacked_vector<B> ) :m_vector(m), m_i(key) {}
	// 	ref & operator=(const B & b) {
	// 		m_vec.emplace_replace(m_i, b);
	// 		return *this;
	// 	}
	// 	ref & operator=(const ref & b) { lean_assert(false); return *this; }
	// 	operator const B&() const {
		
	// 		auto it = m_vec.m_vector.find(m_key);
	// 		lean_assert(it != m_vec.m_vector.end());
	// 		return it->second;
	// 	}
	// };
private:
	void emplace_replace(unsigned a,const B & b) {
		if (!m_stack.empty()) {
			delta & d = m_stack.top();
			auto it = m_vector.find(a);
			if (it == m_vector.end()) {
				d.m_new.insert(a);
				m_vector.emplace(a, b);
			}
			else if (it->second != b) {
				auto nit = d.m_new.find(a);
				if (nit == d.m_new.end()) { // we do not have the old key
					auto & orig_changed = d.m_original_changed;
					auto itt = orig_changed.find(a);
					if (itt == orig_changed.end()) {
						orig_changed.emplace(a, it->second);
					}
					else if (itt->second == b) {
						orig_changed.erase(itt);
					}
				}
				it->second = b;
			}
		}
		else { // there is no stack: just emplace or replace
			m_vector[a] = b;
		}
	}
public:
	// ref operator[] (unsigned a) {
	// 	return ref(*this, a);
	// }

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
				m_vector[t.first] = t.second;
			}
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

