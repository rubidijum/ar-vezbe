#ifndef SOLVER_H
#define SOLVER_H

#include <optional>
#include <istream>
#include "partialvaluation.h"

class Solver
{
public:
    Solver(std::istream& inputStream);

    std::optional<PartialValuation> solve();
private:
    Literal unitClause() const;
    bool conflict() const;

    NormalForm m_formula;
    PartialValuation m_valuation;
};

#endif // SOLVER_H
