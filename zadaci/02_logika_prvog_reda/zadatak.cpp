#include <iostream>
#include <memory>
#include <vector>
#include <map>
#include <set>
#include <functional>

struct Term;
using TermPtr = std::shared_ptr<Term>;

using VariableData = std::string;
struct FunctionData {
    std::string symbol;
    std::vector<TermPtr> args;
};

struct Term {
    enum Type {
        Variable,
        Function
    } type;

    union {
        VariableData variable;
        FunctionData function;
    };

    Term(VariableData d) : type(Variable), variable(d) {}
    Term(FunctionData d) : type(Function), function(d) {}
    ~Term() {
        switch(type) {
        case Variable: variable.~basic_string(); break;
        case Function: function.~FunctionData(); break;
        }
    }
};

struct Formula;
using FormulaPtr = std::shared_ptr<Formula>;

struct TrueData {};
struct FalseData {};
struct AtomData {
    std::string symbol;
    std::vector<TermPtr> args;
};
struct NegData {
    FormulaPtr f;
};
struct BinaryData {
    enum Type {
        And,
        Or,
        Impl,
        Eql
    } type;

    FormulaPtr l, r;
};
struct QuantifierData {
    enum Type {
        All,
        Exists
    } type;

    std::string var;
    FormulaPtr f;
};

struct Formula {
    enum Type {
        True,
        False,
        Atom,
        Neg,
        Binary,
        Quantifier
    } type;

    union {
        AtomData atom;
        NegData neg;
        BinaryData binary;
        QuantifierData quantifier;
    };

    Formula(TrueData)  : type(True)  { }
    Formula(FalseData) : type(False) { }
    Formula(AtomData d) : type(Atom), atom(d) { }
    Formula(NegData d)  : type(Neg), neg(d) {}
    Formula(BinaryData d) : type(Binary), binary(d) {}
    Formula(QuantifierData d) : type(Quantifier), quantifier(d) {}
    ~Formula() {
        switch(type) {
        case Formula::Atom: atom.~AtomData(); break;
        case Formula::Neg:  neg.~NegData(); break;
        case Formula::Binary: binary.~BinaryData(); break;
        case Formula::Quantifier: quantifier.~QuantifierData(); break;
        default: {}
        }
    }
};

struct Signature {
    std::map<std::string, unsigned> fun;
    std::map<std::string, unsigned> rel;
};

using Domain = std::set<unsigned>;
using Valuation = std::map<std::string, unsigned>;
using Function = std::function<unsigned(const std::vector<unsigned>&)>;
using Relation = std::function<bool(const std::vector<unsigned>&)>;

struct LStructure {
    Signature signature;

    Domain domain;
    std::map<std::string, Function> functions;
    std::map<std::string, Relation> relations;
};

unsigned evaluate(TermPtr t, const LStructure& s, const Valuation& v) {
    switch(t->type) {
    case Term::Variable: return v.at(t->variable);
    case Term::Function:
        std::vector<unsigned> args;
        for(TermPtr st : t->function.args)
            args.push_back(evaluate(st, s, v));
        Function f = s.functions.at(t->function.symbol);
        return f(args);
    }
}

bool evaluate(FormulaPtr f, const LStructure& s, const Valuation& v) {
    switch(f->type) {
    case Formula::True: return true;
    case Formula::False:  return false;
    case Formula::Neg:
        return !evaluate(f->neg.f, s, v);
    case Formula::Binary: {
        bool lEval = evaluate(f->binary.l, s, v);
        bool rEval = evaluate(f->binary.r, s, v);

        switch(f->binary.type) {
        case BinaryData::And: return lEval && rEval;
        case BinaryData::Or: return lEval || rEval;
        case BinaryData::Impl: return !lEval || rEval;
        case BinaryData::Eql: return lEval == rEval;
        }
    }
    case Formula::Atom: {
        std::vector<unsigned> args;
        for(TermPtr t : f->atom.args)
            args.push_back(evaluate(t, s, v));
        Relation r = s.relations.at(f->atom.symbol);
        return r(args);
    }
    case Formula::Quantifier:
        std::string var = f->quantifier.var;
        FormulaPtr subf = f->quantifier.f;

        switch(f->quantifier.type) {
        case QuantifierData::All: {
            Valuation val = v;
            for(unsigned value : s.domain) {
                val[var] = value;
                if(!evaluate(subf, s, val))
                    return false;
            }
            return true;
        }
        case QuantifierData::Exists: {
            Valuation val = v;
            for(unsigned value : s.domain) {
                val[var] = value;
                if(evaluate(subf, s, val))
                    return true;
            }
            return false;
        }
        }
    }
}

void print(TermPtr t) {
    switch(t->type) {
    case Term::Variable: std::cout << t->variable; break;
    case Term::Function:
        std::cout << t->function.symbol;
        if(!t->function.args.empty()) {
            std::cout << "(";
            print(t->function.args[0]);
            for(unsigned i = 1; i < t->function.args.size(); i++) {
                std::cout << ", ";
                print(t->function.args[i]);
            }
            std::cout << ")";
        }
    }
}

void print(FormulaPtr f) {
    switch(f->type) {
    case Formula::True: std::cout << "T"; break;
    case Formula::False: std::cout << "F"; break;
    case Formula::Neg:
        std::cout << "~";
        print(f->neg.f);
        break;
    case Formula::Binary:
        std::cout << "(";
        print(f->binary.l);

        switch(f->binary.type) {
        case BinaryData::And: std::cout << " & "; break;
        case BinaryData::Or: std::cout << " | "; break;
        case BinaryData::Impl: std::cout << " -> "; break;
        case BinaryData::Eql: std::cout << " <-> "; break;
        }

        print(f->binary.r);
        std::cout << ")";
        break;
    case Formula::Quantifier:
        switch(f->quantifier.type) {
        case QuantifierData::All: std::cout << "A"; break;
        case QuantifierData::Exists: std::cout << "E"; break;
        }
        std::cout << f->quantifier.var << " ";
        print(f->quantifier.f);
        break;
    case Formula::Atom:
        std::cout << f->atom.symbol;
        if(!f->atom.args.empty()) {
            std::cout << "(";
            print(f->atom.args[0]);
            for(unsigned i = 1; i < f->atom.args.size(); i++) {
                std::cout << ", ";
                print(f->atom.args[i]);
            }
            std::cout << ")";
        }
    }
}

bool checkSignature(TermPtr t, const Signature& s) {
    if(t->type == Term::Variable)
        return true;

    if(s.fun.find(t->function.symbol) == s.fun.end())
        return false;
    if(s.fun.at(t->function.symbol) != t->function.args.size())
        return false;
    for(TermPtr t : t->function.args)
        if(!checkSignature(t, s))
            return false;
    return true;
}

bool checkSignature(FormulaPtr f, const Signature& s) {
    switch(f->type) {
    case Formula::True:
    case Formula::False:
        return true;
    case Formula::Neg:
        return checkSignature(f->neg.f, s);
    case Formula::Binary:
        return checkSignature(f->binary.l, s) &&
               checkSignature(f->binary.r, s);
    case Formula::Quantifier:
        return checkSignature(f->quantifier.f, s);
    case Formula::Atom:
        if(s.rel.find(f->atom.symbol) == s.rel.end())
            return false;
        if(s.rel.at(f->atom.symbol) != f->atom.args.size())
            return false;
        for(TermPtr t : f->atom.args)
            if(!checkSignature(t, s))
                return false;
        return true;
    }
}

int main() {
    return 0;
}
