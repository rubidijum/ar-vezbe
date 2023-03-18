#include <iostream>
#include <variant>
#include <memory>

struct Formula;
using FormulaPtr = std::shared_ptr<Formula>;

struct BinaryData {
    enum class Operator {
        And,
        Or
    } m_op;

    FormulaPtr left;
    FormulaPtr right;

    BinaryData(FormulaPtr l, FormulaPtr r, BinaryData::Operator op): m_op{op}, left{l}, right{r}
    {}
};
struct AtomData { uint16_t n; };
struct NotData { FormulaPtr f; };

struct Formula {
    enum class Type {
        False,
        True,
        Atom,
        Not,
        Binary
    } m_type;

    std::variant<std::monostate, AtomData, NotData, BinaryData> m_data;

    Formula(AtomData a): m_type{Type::Atom}, m_data{std::in_place_type<AtomData>, a} {};
    Formula(NotData d): m_type(Type::Not), m_data{std::in_place_type<NotData>, d} {};
    Formula(BinaryData b): m_type(Type::Binary), m_data{std::in_place_type<BinaryData>, b} {};
};

FormulaPtr Not(FormulaPtr d) { return std::make_shared<Formula>(NotData{d}); }
FormulaPtr Atom(uint16_t a) { return std::make_shared<Formula>(AtomData{a}); }
FormulaPtr Binary(FormulaPtr l, FormulaPtr r, BinaryData::Operator op) { return std::make_shared<Formula>(BinaryData{l, r, op}); }
FormulaPtr And(FormulaPtr l, FormulaPtr r) { return Binary(l, r, BinaryData::Operator::And); }
FormulaPtr Or(FormulaPtr l, FormulaPtr r) { return Binary(l, r, BinaryData::Operator::Or); }

template<class... Lambdas> struct overloaded : Lambdas... {
    using Lambdas::operator()...;
   };

template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

void printFormula(FormulaPtr f){

    std::visit(overloaded{
                   [](AtomData a) { std::cout << "p" << a.n; },
                   [](NotData d) { std::cout << "~";
                                   printFormula(d.f);
                                 },
                   [](BinaryData b) {
                       std::cout << "(";
                       printFormula(b.left);
                       std::cout << (b.m_op == BinaryData::Operator::And ? "^" : "v");
                       printFormula(b.right);
                       std::cout << ")";
                   },
                   [](std::monostate) {
                        return;
                   }
               }, f->m_data);
}

uint16_t depth(FormulaPtr f){
    auto res = std::visit(overloaded{
                   [](AtomData a) { return 1; },
                   [](NotData d) { return (int)depth(d.f); },
                   [](BinaryData b) { return depth(b.left) + depth(b.right); },
                   [](std::monostate) { return 0; }
               }, f->m_data);
    return res;
}

int main()
{

    FormulaPtr p = Atom(1);
    FormulaPtr q = Atom(2);
    FormulaPtr r = Atom(3);

    FormulaPtr f = Or(And(p, Or(Not(q), r)), q);

    printFormula(f);
    std::cout << "\n";
    std::cout << depth(f) << "\n";

    return 0;
}
