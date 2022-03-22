#ifndef VALUATION_H
#define VALUATION_H

#include <map>
#include <set>

class Valuation {
public:

    Valuation(const std::set<unsigned>& atoms);
    void init(const std::set<unsigned>& atoms);
    bool next();

    bool at(unsigned atom) const;
    void print() const;

private:
    std::map<unsigned, bool> m_value;
};

#endif // VALUATION_H
