#include <iostream>
#include <vector>
#include <map>
#include <optional>
#include <sstream>
#include <cassert>

// imena atoma su od 1 do n
// literal je negativan akko je broj negativan
// 0 je specijalan znak
using Atom = int;
using Literal = int;
using Clause = std::vector<Literal>;
using NormalForm = std::vector<Clause>;

struct PartialValuation {

    void push(Literal l, bool decide) {
        if(decide)
            stack.push_back(0);
        stack.push_back(l);

        value[std::abs(l)] = l > 0;
    }

    Literal backtrack() {
        Literal l = 0;
        while(!stack.empty() && stack.back() != 0) {
            l = stack.back();
            stack.pop_back();
            value.erase(std::abs(l));
        }

        if(stack.empty())
            return 0;

        stack.pop_back();
        return l;
    }

    bool isConflict(const Clause& c) {
        for(Literal l : c) {
            Atom atom = std::abs(l);
            if(value.find(atom) == value.end())
                return false;
            if(value[atom] == (l > 0))
                return false;
        }
        return true;
    }

    bool hasConflict(const NormalForm& f) {
        for(const Clause& c : f)
            if(isConflict(c))
                return true;
        return false;
    }

    Literal isUnitClause(const Clause& c) {
        Literal unit = 0;
        for(Literal l : c) {
            Atom atom = std::abs(l);
            if(value.find(atom) == value.end()) {
                if(unit != 0)
                    return 0;
                unit = l;
            }
            else if(value[atom] == (l > 0))
                return 0;
        }
        return unit;
    }

    Literal hasUnitLiteral(const NormalForm& f) {
        Literal l;
        for(const Clause& c : f)
            if((l = isUnitClause(c)) != 0)
                return l;
        return 0;
    }

    Literal nextLiteral() {
        for(int atom = 1; atom <= atomCount; atom++)
            if(value.find(atom) == value.end())
                return atom;
        return 0;
    }

    void print() {
        for(Literal l : stack)
            if(l == 0)
                std::cout << "| ";
            else
                std::cout << l << ' ';
        std::cout << '\n';
    }

    bool isPureLiteral(Literal l, NormalForm& f) {
        for(Clause &c : f){
            for(Literal &_l : c){
                if(l == -1*_l)
                    return false;
            }
        }
        return true;
    }

    int atomCount;
    std::vector<Literal> stack;
    std::map<Atom, bool> value;
};



std::optional<PartialValuation> solve(NormalForm& formula, int atomCount) {
    // pocinjem od prazne valuacije
    // u svakom koraku
    // proveravam konflikt
    //   ako imam konflikt, backtrack
    //   ako imam decide, u valuaciju dodajem negiran decide literal
    //   ako nemam decide, vracam UNSAT
    // proveravam unit clause, ako imam stavljam unit literal u val
    // inace, trazim nedefinisan literal i radim decide
    // ako nema takvog literala: SAT
    PartialValuation valuation;
    valuation.atomCount = atomCount;

    Literal l;
    while(true) {
        valuation.print();
        if(valuation.hasConflict(formula)) {
            l = valuation.backtrack();
            if(l != 0)
                valuation.push(-l, false);
            else
                break;
        }
        else if((l = valuation.hasUnitLiteral(formula)) != 0)
            valuation.push(l, false);
        else if((l = valuation.nextLiteral()) != 0)
            valuation.push(l, true);
        else
            return valuation;
    }
    return {};
}

NormalForm readCNF(std::istream& inputStream, unsigned& atomCount) {
    std::string buffer;
    do {
        inputStream >> buffer;
        if(buffer == "c")
            inputStream.ignore(std::string::npos, '\n');
    } while(buffer != "p");

    // sad je buffer == "p"
    inputStream >> buffer;
    // sad je buffer "cnf"

    unsigned clauseCount;
    inputStream >> atomCount >> clauseCount;

    NormalForm formula;
    for(unsigned i = 0; i < clauseCount; i++) {
        Clause c;

        Literal l;
        inputStream >> l;
        while(l != 0) {
            c.push_back(l);
            inputStream >> l;
        }
        formula.push_back(c);
    }
    return formula;
}

int main()
{
    std::string formula =
            "c ovo je jedan komentar\n"
            "p cnf 3 2\n"
            "1 -2 0\n"
            "-1 -2 3 0\n";
//            "1 -2 0\n"
//            "-1 -2 0\n";
    std::stringstream inputStream(formula);

    unsigned atomCount;
    NormalForm cnf = readCNF(inputStream, atomCount);
    std::optional<PartialValuation> val = solve(cnf, atomCount);

    PartialValuation pureLiteralTest;
    std::cout << "-2 is pure:" << (pureLiteralTest.isPureLiteral(-2, cnf) ? "T" : "F") << "\n";
    std::cout << "3 is pure:" << (pureLiteralTest.isPureLiteral(3, cnf) ? "T" : "F") << "\n";
    std::cout << "1 is pure:" << (pureLiteralTest.isPureLiteral(1, cnf) ? "T" : "F") << "\n";
    std::cout << "2 is pure:" << (pureLiteralTest.isPureLiteral(2, cnf) ? "T" : "F") <<"\n";


    if(val) {
        std::cout << "SAT\n";
        val.value().print();
    }
    else
        std::cout << "UNSAT\n";
    return 0;
}
