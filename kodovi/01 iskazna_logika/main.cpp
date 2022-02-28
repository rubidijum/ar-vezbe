#include <iostream>
#include <memory>
#include <map>

struct Formula;
using FormulaPtr = std::shared_ptr<Formula>;
using Valuation = std::map<unsigned, bool>;

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

    union Data {
        AtomData atomData;
        NotData notData;
        BinaryData binaryData;

        Data() {}
        ~Data() {}
    } data;

    Formula(FalseData)    : type(False)  { }
    Formula(TrueData)     : type(True)   { }
    Formula(AtomData d)   : type(Atom)   { data.atomData = d; }
    Formula(NotData d)    : type(Not)    { data.notData = d; }
    Formula(BinaryData d) : type(Binary) { data.binaryData = d; }
};

FormulaPtr False() { return std::make_shared<Formula>(FalseData{}); }
FormulaPtr True()  { return std::make_shared<Formula>(TrueData{}); }
FormulaPtr Atom(unsigned n) { return std::make_shared<Formula>(AtomData{n}); }
FormulaPtr Not(FormulaPtr f) { return std::make_shared<Formula>(NotData{f}); }
FormulaPtr Binary(BinaryData::Type t, FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{t, l, r});
}
FormulaPtr And(FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{BinaryData::Type::And, l, r});
}
FormulaPtr Or(FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{BinaryData::Type::Or, l, r});
}
FormulaPtr Impl(FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{BinaryData::Type::Impl, l, r});
}
FormulaPtr Eql(FormulaPtr l, FormulaPtr r) {
    return std::make_shared<Formula>(BinaryData{BinaryData::Type::Eql, l, r});
}

void printFormula(FormulaPtr formula) {
    switch(formula->type) {
    case Formula::Type::False: std::cout << "F"; break;
    case Formula::Type::True:  std::cout << "T"; break;

    case Formula::Type::Atom:
        std::cout << "p" << formula->data.atomData.n;
        break;

    case Formula::Type::Not:
        std::cout << "~";
        printFormula(formula->data.notData.f);
        break;

    case Formula::Type::Binary:
        std::cout << "(";
        printFormula(formula->data.binaryData.l);

        switch(formula->data.binaryData.type) {
        case BinaryData::Type::And:  std::cout << " & "; break;
        case BinaryData::Type::Or:   std::cout << " | "; break;
        case BinaryData::Type::Impl: std::cout << " -> "; break;
        case BinaryData::Type::Eql:  std::cout << " <-> "; break;
        }

        printFormula(formula->data.binaryData.r);
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
        return 1 + complexity(formula->data.notData.f);
    case Formula::Type::Binary:
        return 1 + complexity(formula->data.binaryData.l)
                 + complexity(formula->data.binaryData.r);
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
        return f->data.atomData.n == g->data.atomData.n;
    case Formula::Type::Not:
        return equal(f->data.notData.f, g->data.notData.f);
    case Formula::Type::Binary:
        if(f->data.binaryData.type != g->data.binaryData.type)
            return false;
        return equal(f->data.binaryData.l, g->data.binaryData.l) &&
               equal(f->data.binaryData.r, g->data.binaryData.r);
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
        return Not(substitute(formula->data.notData.f, what, with));
    case Formula::Type::Binary:
        FormulaPtr lSub = substitute(formula->data.binaryData.l, what, with);
        FormulaPtr rSub = substitute(formula->data.binaryData.r, what, with);
        return Binary(formula->data.binaryData.type, lSub, rSub);
    }
}

bool evaluate(FormulaPtr formula, const Valuation& val) {
    switch(formula->type) {
    case Formula::Type::False: return false;
    case Formula::Type::True:  return true;
    case Formula::Type::Atom:  return val.at(formula->data.atomData.n);
    case Formula::Type::Not:   return !evaluate(formula->data.notData.f, val);
    case Formula::Type::Binary:
        bool lEval = evaluate(formula->data.binaryData.l, val);
        bool rEval = evaluate(formula->data.binaryData.r, val);
        switch(formula->data.binaryData.type) {
        case BinaryData::Type::And:  return lEval && rEval;
        case BinaryData::Type::Or:   return lEval || rEval;
        case BinaryData::Type::Impl: return !lEval || rEval;
        case BinaryData::Type::Eql:  return lEval == rEval;
        }
    }
}

// (p0 & p1) -> ~p2
int main()
{
    FormulaPtr p0 = Atom(0);
    FormulaPtr p1 = Atom(1);
    FormulaPtr p2 = Atom(2);
    FormulaPtr leftF = And(p0, p1);
    FormulaPtr rightF = Not(p2);
    FormulaPtr F = Impl(leftF, rightF);

    printFormula(F); std::cout << std::endl;
    std::cout << complexity(F) << std::endl;

    return 0;
}
