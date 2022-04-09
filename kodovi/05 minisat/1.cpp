#include <iostream>
#include <vector>

using namespace std;

using Clause = vector<int>;
using NormalForm = vector<Clause>;

int p(int i) { return 2 * i + 1; }
int q(int i) { return 2 * i + 2; }

int varCount = 0;
NormalForm formula;

void clause(const Clause& c) {
	formula.push_back(c);
	for(auto& literal : c)
		varCount = max(varCount, abs(literal));
}

void R(int i, int j) {
	clause({ -q(j), -q(i) });
	clause({ q(j), q(i) });
	clause({ -p(j), p(i), q(i) });
	clause({ -p(j), -p(i), -q(i) });
	clause({ p(j), p(i), -q(i) });
	clause({ p(j), -p(i), q(i) });
}

void nJ(int i, int j) {
	clause({ p(i), p(j), q(i), q(j) });
	clause({ p(i), p(j), -q(i), -q(j) });
	clause({ -p(i), -p(j), q(i), q(j) });
	clause({ -p(i), -p(j), -q(i), -q(j) });
}

int main() {
	R(0, 1);
	R(1, 2);
	R(2, 3);
	R(3, 4);
	nJ(0, 4);
	// c ovo je jedan komentar
	// p cnf varCount clauseCount
	// 1 -2 3 0 <- p1 ili ne p2 ili p3
	cout << "p cnf " << varCount << ' ' << formula.size() << endl;
	for(auto& c : formula) {
		for(auto& l : c)
			cout << l << ' ';
		cout << 0 << endl;
	}
	return 0;
}
