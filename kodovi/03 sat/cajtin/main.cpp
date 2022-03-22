#include <iostream>
#include "formula.h"

int main()
{
    // Tablica istinitosti
    // p0 & ~p1
    FormulaPtr f = And(Atom(0), Not(Atom(1)));
    printFormula(f); std::cout << std::endl;
    printTable(f);

    auto val = isSatisfiable(f);
    if(val)
        val->print();
    else
        std::cout << "UNSAT" << std::endl;

    // Svodjenje na KNF
    // (~p0 -> (p1 | F)) -> (~p0 & (p2 & T))
    std::cout << "Formula" << std::endl;
    FormulaPtr g = Impl(Impl(Not(Atom(0)), Or(Atom(1), False())), And(Not(Atom(0)), And(Atom(2), True())));
    printFormula(g); std::cout << std::endl;

    std::cout << "Simplified" << std::endl;
    FormulaPtr gSimp = simplify(g);
    printFormula(gSimp); std::cout << std::endl;

    std::cout << "NNF" << std::endl;
    FormulaPtr gNNF = nnf(gSimp);
    printFormula(gNNF); std::cout << std::endl;

    std::cout << "CNF" << std::endl;
    NormalForm gCNF = cnf(gNNF);
    for(const auto& clause : gCNF) {
        for(const auto& literal : clause)
            std::cout << (literal.positive ? "p" : "~p") << literal.atom << ' ';
        std::cout << std::endl;
    }

    // Cajtinova transformacija za svodjenje na KNF
    std::cout << "Tseitin CNF" << std::endl;
    NormalForm tseitinCNF = tseitin(g);
    for(const auto& clause : tseitinCNF) {
        for(const auto& literal : clause)
            std::cout << (literal.positive ? "p" : "~p") << literal.atom << ' ';
        std::cout << std::endl;
    }

    return 0;
}
