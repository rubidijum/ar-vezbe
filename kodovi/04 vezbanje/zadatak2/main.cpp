#include <iostream>
#include <memory>
#include <optional>

#include "valuation.h"

using namespace std;

struct Formula;
using FormulaPtr = std::shared_ptr<Formula>;

struct AtomData { unsigned n; };
struct NotData { FormulaPtr f; };
struct BinaryData {
    enum Type {
        And,
        Or,
        Impl
    } type;

    FormulaPtr l;
    FormulaPtr r;
};

struct Formula {
    // tip cvora stabla (bilo da je veznik ili atom)
    // podatke za taj tip cvora

    enum Type {
        Atom,
        Not,
        Binary
    } type;

    union {
        AtomData atomData;
        NotData notData;
        BinaryData binaryData;
    };

    Formula(AtomData d) : type(Atom), atomData(d) {}
    Formula(NotData d) : type(Not), notData(d) {}
    Formula(BinaryData d) : type(Binary), binaryData(d) {}
    ~Formula() {
        switch(type) {
        case Atom:   atomData.~AtomData(); break;
        case Not:    notData.~NotData(); break;
        case Binary: binaryData.~BinaryData(); break;
        }
    }
};

FormulaPtr Atom(unsigned n) { return std::make_shared<Formula>(AtomData{n}); }
FormulaPtr Not(FormulaPtr f) { return std::make_shared<Formula>(NotData{f}); }
FormulaPtr And(FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{BinaryData::And, l, r});
}
FormulaPtr Or(FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{BinaryData::Or, l, r});
}
FormulaPtr Impl(FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{BinaryData::Impl, l, r});
}

void printFormula(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Atom:
        cout << "p" << formula->atomData.n;
        break;
    case Formula::Not:
        cout << "~";
        printFormula(formula->notData.f);
        break;
    case Formula::Binary:
        cout << "(";
        printFormula(formula->binaryData.l);

        switch(formula->binaryData.type) {
        case BinaryData::And:  cout << " & "; break;
        case BinaryData::Or:   cout << " | "; break;
        case BinaryData::Impl: cout << " -> "; break;
        }

        printFormula(formula->binaryData.r);
        cout << ")";
    }
}

void getAtoms(FormulaPtr formula, std::set<unsigned>& atoms) {
    switch(formula->type) {
    case Formula::Atom:
        atoms.insert(formula->atomData.n);
        break;
    case Formula::Not:
        getAtoms(formula->notData.f, atoms);
        break;
    case Formula::Binary:
        getAtoms(formula->binaryData.l, atoms);
        getAtoms(formula->binaryData.r, atoms);
        break;
    }
}

bool evaluate(FormulaPtr formula, const Valuation& val) {
    switch(formula->type) {
    case Formula::Atom:
        return val.at(formula->atomData.n);
    case Formula::Not:
        return !evaluate(formula->notData.f, val);
    case Formula::Binary:
        bool lEval = evaluate(formula->binaryData.l, val);
        bool rEval = evaluate(formula->binaryData.r, val);
        switch(formula->binaryData.type) {
        case BinaryData::And:  return lEval && rEval;
        case BinaryData::Or:   return lEval || rEval;
        case BinaryData::Impl: return !lEval || rEval;
        }
    }
}

bool isConseqence(const std::set<FormulaPtr>& D, FormulaPtr formula) {
    std::set<unsigned> atoms;
    for(auto& f : D)
        getAtoms(f, atoms);
    getAtoms(formula, atoms);

    Valuation val(atoms);
    do {
        bool evalD = true;
        for(auto& f : D)
            evalD = evalD && evaluate(f, val);
        if(evalD && !evaluate(formula, val))
            return false;
    } while(val.next());
    return true;
}

std::optional<FormulaPtr> isIndependent(const std::set<FormulaPtr>& D) {
    std::set<FormulaPtr> DCopy(D);
    for(auto& formula : D) {
        DCopy.erase(formula);
        if(isConseqence(DCopy, formula))
            return formula;
        DCopy.insert(formula);
    }
    return {};
}

std::set<FormulaPtr> minimize(const std::set<FormulaPtr>& D) {
    std::set<FormulaPtr> minimized(D);
    std::optional<FormulaPtr> dependentFormula;
    while((dependentFormula = isIndependent(minimized)))
        minimized.erase(dependentFormula.value());
    return minimized;
}

int main() {
    FormulaPtr p = Atom(0), q = Atom(1), r = Atom(2), s = Atom(3);
    FormulaPtr f1 = Or(Not(p), q);
    FormulaPtr f2 = Impl(Not(Impl(r, s)), Impl(p, q));
    FormulaPtr f3 = Impl(Not(q), Not(p));
    std::set<FormulaPtr> formulae = {f1, f2, f3};
    auto minimized = minimize(formulae);
    for(auto& formula : minimized) {
        printFormula(formula);
        cout << endl;
    }
    return 0;
}
