#include "formula.h"

#include <iostream>
#include <set>
#include <optional>
#include "valuation.h"

FormulaPtr False() { return std::make_shared<Formula>(FalseData{}); }
FormulaPtr True()  { return std::make_shared<Formula>(TrueData{}); }
FormulaPtr Atom(unsigned n) { return std::make_shared<Formula>(AtomData{n}); }
FormulaPtr Not(FormulaPtr f) { return std::make_shared<Formula>(NotData{f}); }
FormulaPtr Binary(BinaryData::Type t, FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{t, l, r});
}
FormulaPtr And(FormulaPtr l, FormulaPtr r)  { return Binary(BinaryData::Type::And,  l, r); }
FormulaPtr Or(FormulaPtr l, FormulaPtr r)   { return Binary(BinaryData::Type::Or,   l, r); }
FormulaPtr Impl(FormulaPtr l, FormulaPtr r) { return Binary(BinaryData::Type::Impl, l, r); }
FormulaPtr Eql(FormulaPtr l, FormulaPtr r)  { return Binary(BinaryData::Type::Eql,  l, r); }


void printFormula(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::False: std::cout << "F"; break;
    case Formula::Type::True:  std::cout << "T"; break;

    case Formula::Type::Atom:
        std::cout << "p" << formula->atomData.n;
        break;

    case Formula::Type::Not:
        std::cout << "~";
        printFormula(formula->notData.f);
        break;

    case Formula::Type::Binary:
        std::cout << "(";
        printFormula(formula->binaryData.l);

        switch(formula->binaryData.type) {
        case BinaryData::Type::And:  std::cout << " & "; break;
        case BinaryData::Type::Or:   std::cout << " | "; break;
        case BinaryData::Type::Impl: std::cout << " -> "; break;
        case BinaryData::Type::Eql:  std::cout << " <-> "; break;
        }

        printFormula(formula->binaryData.r);
        std::cout << ")";
        break;
    }
}

unsigned complexity(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::False:
    case Formula::Type::True:
    case Formula::Type::Atom:
        return 0;
    case Formula::Type::Not:
        return 1 + complexity(formula->notData.f);
    case Formula::Type::Binary:
        return 1 + complexity(formula->binaryData.l)
                 + complexity(formula->binaryData.r);
    }
}

bool equal(FormulaPtr f, FormulaPtr g) {
    if(f->type != g->type)
        return false;

    switch(f->type) {
    case Formula::Type::True:
    case Formula::Type::False:
        return true;
    case Formula::Type::Atom:
        return f->atomData.n == g->atomData.n;
    case Formula::Type::Not:
        return equal(f->notData.f, g->notData.f);
    case Formula::Type::Binary:
        if(f->binaryData.type != g->binaryData.type)
            return false;
        return equal(f->binaryData.l, g->binaryData.l) &&
               equal(f->binaryData.r, g->binaryData.r);
    }
}

FormulaPtr substitute(FormulaPtr formula, FormulaPtr what, FormulaPtr with) {
    if(equal(formula, what))
        return with;

    switch(formula->type) {
    case Formula::Type::True:
    case Formula::Type::False:
    case Formula::Type::Atom:
        return formula;
    case Formula::Type::Not:
        return Not(substitute(formula->notData.f, what, with));
    case Formula::Type::Binary:
        FormulaPtr lSub = substitute(formula->binaryData.l, what, with);
        FormulaPtr rSub = substitute(formula->binaryData.r, what, with);
        return Binary(formula->binaryData.type, lSub, rSub);
    }
}

bool evaluate(FormulaPtr formula, const Valuation& val) {
    switch(formula->type) {
    case Formula::Type::False: return false;
    case Formula::Type::True:  return true;
    case Formula::Type::Atom:  return val.at(formula->atomData.n);
    case Formula::Type::Not:   return !evaluate(formula->notData.f, val);
    case Formula::Type::Binary: {
        bool lEval = evaluate(formula->binaryData.l, val);
        bool rEval = evaluate(formula->binaryData.r, val);
        switch(formula->binaryData.type) {
        case BinaryData::Type::And:  return lEval && rEval;
        case BinaryData::Type::Or:   return lEval || rEval;
        case BinaryData::Type::Impl: return !lEval || rEval;
        case BinaryData::Type::Eql:  return lEval == rEval;
        }
    }
    }
}

// --- Drugi cas ---

void getAtoms(FormulaPtr formula, std::set<unsigned> &atoms) {
    switch(formula->type) {
    case Formula::Type::True:
    case Formula::Type::False:
        return;
    case Formula::Type::Atom:
        atoms.insert(formula->atomData.n);
        return;
    case Formula::Type::Not:
        getAtoms(formula->notData.f, atoms);
        return;
    case Formula::Type::Binary:
        getAtoms(formula->binaryData.l, atoms);
        getAtoms(formula->binaryData.r, atoms);
        return;
    }
}

void printTable(FormulaPtr formula) {
    std::set<unsigned> atoms;
    getAtoms(formula, atoms);

    Valuation val(atoms);
    do {
        val.print();
        std::cout << "| " << evaluate(formula, val) << std::endl;
    } while(val.next());
}

std::optional<Valuation> isSatisfiable(FormulaPtr formula) {
    std::set<unsigned> atoms;
    getAtoms(formula, atoms);

    Valuation val(atoms);
    do {
        if(evaluate(formula, val))
            return val;
    } while(val.next());
    return {};
}

bool isEquivalent(FormulaPtr f, FormulaPtr g) {
    std::set<unsigned> atoms;
    getAtoms(f, atoms);
    getAtoms(g, atoms);

    Valuation val(atoms);
    do {
        if(evaluate(f, val) != evaluate(g, val))
            return false;
    } while(val.next());
    return true;
}

FormulaPtr simplifyNot(FormulaPtr formula) {
    FormulaPtr subformula = simplify(formula->notData.f);
    switch(subformula->type) {
    case Formula::Type::True:
        return False();
    case Formula::Type::False:
        return True();
    default:
        return Not(subformula);
    }
}

FormulaPtr simplifyAnd(FormulaPtr formula) {
    FormulaPtr sLeft  = simplify(formula->binaryData.l);
    FormulaPtr sRight = simplify(formula->binaryData.r);

    if(sLeft->type == Formula::Type::False ||
       sRight->type == Formula::Type::False)
        return False();

    if(sLeft->type == Formula::Type::True)
        return sRight;
    if(sRight->type == Formula::Type::True)
        return sLeft;

    return And(sLeft, sRight);
}

FormulaPtr simplifyOr(FormulaPtr formula) {
    FormulaPtr sLeft  = simplify(formula->binaryData.l);
    FormulaPtr sRight = simplify(formula->binaryData.r);

    if(sLeft->type == Formula::Type::True ||
       sRight->type == Formula::Type::True)
        return True();

    if(sLeft->type == Formula::Type::False)
        return sRight;
    if(sRight->type == Formula::Type::False)
        return sLeft;

    return Or(sLeft, sRight);
}

FormulaPtr simplifyImpl(FormulaPtr formula) {
    FormulaPtr sLeft  = simplify(formula->binaryData.l);
    FormulaPtr sRight = simplify(formula->binaryData.r);

    if(sLeft->type == Formula::Type::False ||
       sRight->type == Formula::Type::True)
        return True();

    if(sLeft->type == Formula::Type::True)
        return sRight;
    if(sRight->type == Formula::Type::False)
        return simplify(Not(sLeft));

    return Impl(sLeft, sRight);
}

FormulaPtr simplifyEql(FormulaPtr formula) {
    FormulaPtr sLeft  = simplify(formula->binaryData.l);
    FormulaPtr sRight = simplify(formula->binaryData.r);

    if(sLeft->type == Formula::Type::True)
        return sRight;
    if(sRight->type == Formula::Type::True)
        return sLeft;
    if(sLeft->type == Formula::Type::False)
        return simplify(Not(sRight));
    if(sRight->type == Formula::Type::False)
        return simplify(Not(sLeft));

    return Eql(sLeft, sRight);
}

FormulaPtr simplify(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::True:
    case Formula::Type::False:
    case Formula::Type::Atom:
        return formula;
    case Formula::Type::Not:
        return simplifyNot(formula);
    case Formula::Type::Binary:
        switch(formula->binaryData.type) {
        case BinaryData::Type::And:  return simplifyAnd(formula);
        case BinaryData::Type::Or:   return simplifyOr(formula);
        case BinaryData::Type::Impl: return simplifyImpl(formula);
        case BinaryData::Type::Eql:  return simplifyEql(formula);
        }
    }
}

FormulaPtr nnfNot(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::Atom:
        return Not(formula);
    case Formula::Type::Not:
        return nnf(formula->notData.f);
    case Formula::Type::Binary: {
        FormulaPtr l = formula->binaryData.l;
        FormulaPtr r = formula->binaryData.r;
        switch(formula->binaryData.type) {
        case BinaryData::Type::And:
            return Or(nnf(Not(l)), nnf(Not(r)));
        case BinaryData::Type::Or:
            return And(nnf(Not(l)), nnf(Not(r)));
        case BinaryData::Type::Impl:
            return And(nnf(l), nnf(Not(r)));
        case BinaryData::Type::Eql:
            return Or(And(nnf(l), nnf(Not(r))), And(nnf(r), nnf(Not(l))));
        }
    }
    default:
        return nullptr;
    }
}

FormulaPtr nnf(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::True:
    case Formula::Type::False:
    case Formula::Type::Atom:
        return formula;
    case Formula::Type::Not:
        return nnfNot(formula->notData.f);
    case Formula::Type::Binary:
        FormulaPtr l = formula->binaryData.l;
        FormulaPtr r = formula->binaryData.r;
        switch(formula->binaryData.type) {
        case BinaryData::Type::And:
            return And(nnf(l), nnf(r));
        case BinaryData::Type::Or:
            return Or(nnf(l), nnf(r));
        case BinaryData::Type::Impl:
            return Or(nnf(Not(l)), nnf(r));
        case BinaryData::Type::Eql:
            return And(Or(nnf(Not(l)), nnf(r)), Or(nnf(Not(r)), nnf(l)));
        }
    }
}

template<typename ListType>
ListType concat(const ListType& l, const ListType& r) {
    ListType result;
    std::copy(begin(l), end(l), back_inserter(result));
    std::copy(begin(r), end(r), back_inserter(result));
    return result;
}

NormalForm cross(const NormalForm& l, const NormalForm& r) {
    NormalForm result;
    for(const auto& c1 : l)
        for(const auto& c2 : r)
            result.push_back(concat(c1, c2));
    return result;
}

NormalForm cnf(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::True:  return {};
    case Formula::Type::False: return {{}};
    case Formula::Type::Atom:  return {{ Literal{true, formula->atomData.n} }};
    case Formula::Type::Not:   return {{ Literal{false, formula->notData.f->atomData.n} }};
    case Formula::Type::Binary:
        switch(formula->binaryData.type) {
        case BinaryData::Type::And: return concat(cnf(formula->binaryData.l), cnf(formula->binaryData.r)); // nadovezi cnf(l) i cnf(r)
        case BinaryData::Type::Or:  return cross(cnf(formula->binaryData.l), cnf(formula->binaryData.r)); // proizvod cnf(l) i cnf(r)
        default: return {};
        }
    }
}

// --- Treci cas ---
unsigned tseitin(FormulaPtr formula, NormalForm& cnf, unsigned& atom) {
    switch(formula->type) {
    case Formula::Type::True:
        cnf.push_back({ Literal{true, atom} });
        return atom++;
    case Formula::Type::False:
        cnf.push_back({ Literal{false, atom} });
        return atom++;
    case Formula::Type::Atom:
        return formula->atomData.n;
    case Formula::Type::Not: {
        unsigned subformula = tseitin(formula->notData.f, cnf, atom);
        NormalForm tseitinNot = { {Literal{false, subformula}, Literal{false, atom}},
                                  {Literal{true, subformula}, Literal{true, atom}} };
        std::copy(begin(tseitinNot), end(tseitinNot), std::back_inserter(cnf));
        return atom++;
    }
    default: {}
    }

    unsigned l = tseitin(formula->binaryData.l, cnf, atom);
    unsigned r = tseitin(formula->binaryData.r, cnf, atom);

    NormalForm tseitinBinary;
    switch(formula->binaryData.type) {
    case BinaryData::Type::And:
        tseitinBinary = { { Literal{false, atom}, Literal{true, l} },
                          { Literal{false, atom}, Literal{true, r} },
                          { Literal{true, atom}, Literal{false, l}, Literal{false, r} }};
        break;
    case BinaryData::Type::Or:
        tseitinBinary = { { Literal{false, atom}, Literal{true, l}, Literal{true, r} },
                          { Literal{true, atom}, Literal{false, l} },
                          { Literal{true, atom}, Literal{false, r} } };
        break;
    case BinaryData::Type::Impl:
        tseitinBinary = { /* Za domaci */ };
        break;
    case BinaryData::Type::Eql:
        tseitinBinary = { { Literal{false, atom}, Literal{false, l}, Literal{true, r} },
                          { Literal{false, atom}, Literal{true, l}, Literal{false, r} },
                          { Literal{true, atom}, Literal{true, l}, Literal{true, r} },
                          { Literal{true, atom}, Literal{false, l}, Literal{false, r} } };
        break;
    }

    std::copy(begin(tseitinBinary), end(tseitinBinary), std::back_inserter(cnf));
    return atom++;
}

NormalForm tseitin(FormulaPtr formula) {
    std::set<unsigned> atoms;
    getAtoms(formula, atoms);
    unsigned atom = *atoms.rbegin() + 1;

    NormalForm cnf = {};
    unsigned s = tseitin(formula, cnf, atom);
    cnf.push_back({Literal{true, s}});

    return cnf;
}
