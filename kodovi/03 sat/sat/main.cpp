#include <iostream>
#include <sstream>
#include "solver.h"

using namespace std;

int main() {
    string input =
            "c ovo je jedan komentar\n"
            "p cnf 3 4\n"
            "1 -2 0\n"
            "-1 2 3 0\n"
            "-2 3 0\n"
            "-1 -3 0\n";
    stringstream inputStream(input);
    Solver sat(inputStream);
    std::optional<PartialValuation> model = sat.solve();
    if(model) {
        cout << "SAT\n";
        model.value().print();
    }
    else
        cout << "UNSAT\n";
    return 0;
}
