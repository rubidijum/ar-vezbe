#ifndef PARTIALVALUATION_H
#define PARTIALVALUATION_H

#include <vector>

using Literal = int;
using Clause = std::vector<Literal>;
using NormalForm = std::vector<Clause>;

const Literal NullLiteral = 0;

enum class TriBool {
    False,
    True,
    Undefined
};

class PartialValuation
{
public:
    PartialValuation(unsigned varCount = 0);
    void init(unsigned varCount);

    void push(Literal l, bool decide);
    Literal backtrack();

    Literal nextLiteral() const;
    bool isConflict(const Clause& clause) const;
    Literal isUnitClause(const Clause& clause) const;

    void print() const;

private:
    std::vector<Literal> m_stack;
    std::vector<TriBool> m_value;
};

#endif // PARTIALVALUATION_H
