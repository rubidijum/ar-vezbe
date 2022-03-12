#include "valuation.h"

#include <iostream>

Valuation::Valuation(const std::set<unsigned> &atoms) {
    init(atoms);
}

void Valuation::init(const std::set<unsigned> &atoms) {
    m_value.clear();
    for(auto atom : atoms)
        m_value[atom] = false;
}

bool Valuation::next() {
    auto it = m_value.rbegin();
    while(it != m_value.rend() && it->second) {
        it->second = false;
        it++;
    }
    if(it == m_value.rend())
        return false;
    it->second = true;
    return true;
}

bool Valuation::at(unsigned atom) const {
    return m_value.at(atom);
}

void Valuation::print() const {
    for(auto atom : m_value)
        std::cout << atom.second << ' ';
}
