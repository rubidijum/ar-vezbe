#include <iostream>
#include <memory>

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

unsigned nnfDistance(FormulaPtr formula, unsigned& depth) {
    switch(formula->type) {
    case Formula::Atom: {
        depth = 0;
        return 0;
    }
    case Formula::Binary: {
        unsigned depthL, depthR;
        unsigned l = nnfDistance(formula->binaryData.l, depthL);
        unsigned r = nnfDistance(formula->binaryData.r, depthR);
        depth = std::max(depthL, depthR) + 1;
        return l + r;
    }
    case Formula::Not: {
        unsigned depthSubformula;
        unsigned nnfSubformula = nnfDistance(formula->notData.f, depthSubformula);
        depth = depthSubformula + 1;
        return nnfSubformula + depthSubformula;
    }
    }
}

int main() {
    FormulaPtr x = Atom(0), y = Atom(1), z = Atom(2);
    FormulaPtr f = And(Not(Impl(x, Or(y, Not(z)))), Not(Or(Not(x), Not(Impl(y, z)))));

    printFormula(f); cout << endl;
    unsigned depth;
    cout << nnfDistance(f, depth) << endl;
    return 0;
}
