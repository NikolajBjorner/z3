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
#pragma once
namespace lp {
class explanation {
    vector<std::pair<mpq, constraint_index>> m_explanation;
    std::unordered_set<unsigned> m_set_of_ci;
public:
    void clear() { m_explanation.clear(); m_set_of_ci.clear(); }
    vector<std::pair<mpq, constraint_index>>::const_iterator begin() const { return m_explanation.begin(); }
    vector<std::pair<mpq, constraint_index>>::const_iterator end() const { return m_explanation.end(); }
    void push_justification(constraint_index j, const mpq& v) {
        m_explanation.push_back(std::make_pair(v, j));
    }
    void push_justification(constraint_index j) {
        if (m_set_of_ci.find(j) != m_set_of_ci.end()) return;
        m_set_of_ci.insert(j);
        m_explanation.push_back(std::make_pair(one_of_type<mpq>(), j));
    }
    void reset() { m_explanation.reset(); }
    template <typename A> void add(const A& a) { for (constraint_index j : a) push_justification(j); }
};
}
