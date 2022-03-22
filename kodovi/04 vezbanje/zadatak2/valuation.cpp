#include "valuation.h"

Valuation::Valuation(const std::set<unsigned>& atoms) {
    for(auto& atom : atoms)
        m_value[atom] = false;
}

bool Valuation::next() {
    auto it = m_value.rbegin();
    while(it != m_value.rend() && it->second == true) {
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
