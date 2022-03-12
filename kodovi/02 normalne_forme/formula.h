#ifndef FORMULA_H
#define FORMULA_H

#include <iostream>
#include <memory>
#include <map>
#include <set>
#include <optional>
#include <vector>

#include "valuation.h"

struct Formula;
using FormulaPtr = std::shared_ptr<Formula>;

struct FalseData  { };
struct TrueData   { };
struct AtomData   { unsigned n; };
struct NotData    { FormulaPtr f; };
struct BinaryData {
    enum Type {
        And,
        Or,
        Impl,
        Eql
    } type;

    FormulaPtr l;
    FormulaPtr r;
};

struct Formula {
    enum Type {
        False,
        True,
        Atom,
        Not,
        Binary
    } type;

    union {
        AtomData atomData;
        NotData notData;
        BinaryData binaryData;
    };

    Formula(FalseData)    : type(False)                 { }
    Formula(TrueData)     : type(True)                  { }
    Formula(AtomData d)   : type(Atom), atomData(d)     { }
    Formula(NotData d)    : type(Not), notData(d)       { }
    Formula(BinaryData d) : type(Binary), binaryData(d) { }
    ~Formula() {
        switch(type) {
        case Not: notData.~NotData(); break;
        case Binary: binaryData.~BinaryData(); break;
        default: {}
        }
    }
};

FormulaPtr False();
FormulaPtr True();
FormulaPtr Atom(unsigned n);
FormulaPtr Not(FormulaPtr f);
FormulaPtr Binary(BinaryData::Type t, FormulaPtr l, FormulaPtr r);
FormulaPtr And(FormulaPtr l, FormulaPtr r);
FormulaPtr Or(FormulaPtr l, FormulaPtr r);
FormulaPtr Impl(FormulaPtr l, FormulaPtr r);
FormulaPtr Eql(FormulaPtr l, FormulaPtr r);


// --- Prvi cas ---
void printFormula(FormulaPtr formula);
unsigned complexity(FormulaPtr formula);
bool equal(FormulaPtr f, FormulaPtr g);
FormulaPtr substitute(FormulaPtr formula, FormulaPtr what, FormulaPtr with);
bool evaluate(FormulaPtr formula, const Valuation& val);

// --- Drugi cas ---
void getAtoms(FormulaPtr formula, std::set<unsigned>& atoms);
void printTable(FormulaPtr formula);
std::optional<Valuation> isSatisfiable(FormulaPtr formula);
// std::optional<Valuation> isFalsifiable(FormulaPtr formula); - slicno
bool isEquivalent(FormulaPtr f, FormulaPtr g);
// bool isConsequence(FormulaPtr f, FormulaPtr g); - slicno

struct Literal {
    bool positive;
    unsigned atom;
};
using Clause = std::vector<Literal>;
using NormalForm = std::vector<Clause>;

FormulaPtr simplify(FormulaPtr formula);
FormulaPtr nnf(FormulaPtr formula);
NormalForm cnf(FormulaPtr formula);
// NormalForm dnf(FormulaPtr formula);

#endif // FORMULA_H
