## 03 Cajtinova transformacija i čist literal

Rok za predaju:  *28.3.2022* \
Naslov mejla:    *[AR] Domaći zadatak 03_sat* \
U prilogu mejla: *Sve potrebne .cpp i .h datoteke*

Kod sa trećeg tročasa vežbi proširiti narednim funkcionalnostima.

1. U okviru projekta *cajtin* po uzoru na ostale slučajeve dopuniti
implementaciju funkcije `tseitin` pokrivanjem slučaja implikacije.
1. U okviru projekta *sat* implementirati metodu `bool isPureLiteral(Literal
l)` klase `Solver` kojom se proverava da li se literal `l` pojavljuje samo
u datom polaritetu u formuli `m_formula`. Na primer, u formuli `{{1, -2}, {-1,
-2, 3}}` pozivi funkcije `isPureLiteral(-2)` i `isPureLiteral(3)` vraćaju
`true`, dok pozivi `isPureLiteral(1)` i `isPureLiteral(2)` vraćaju `false`.
