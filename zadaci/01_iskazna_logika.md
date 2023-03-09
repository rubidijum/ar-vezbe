## 01 Iskazna logika

Rok za predaju:  *19.3.2022* \
Naslov mejla:    *[AR] Domaći zadatak 01_iskazna_logika* \
U prilogu mejla: *dubina.cpp i sat.cpp (i dodatne datoteke po izboru)*

### Dubina iskazne formule

1. Implementirati strukture za predstavljanje iskaznih formula koje se sastoje
iz atoma, negacije, konjunkcije i disjunkcije.
1. Dubina čvora u stablu definiše se kao broj grana na jedinstvenom putu od
korena stabla do tog čvora. Dubina stabla definiše se kao maksimum dubina svih
čvorova. Dubina iskazne formule definiše se kao dubina stabla kojim je formula
predstavljena. Implementirati funkciju kojom se određuje dubina zadate iskazne
formule.
1. U `main` funkciji programa definisati formulu `(p & (~q | r)) | q` i na
standardni izlaz ispisati njenu dubinu. Očekivani izlaz je `4`.

### Čist literal

1. U okviru fajla *kodovi/03 sat/sat/main.cpp* implementirati funkciju `bool
isPureLiteral(Literal l, NormalForm& f)` kojom se proverava da li se literal
`l` pojavljuje samo u datom polaritetu u formuli `f`. Na primer, u formuli
`{{1, -2}, {-1, -2, 3}}` pozivi funkcije `isPureLiteral(-2, f)` i
`isPureLiteral(3, f)` vraćaju `true`, dok pozivi `isPureLiteral(1, f)` i
`isPureLiteral(2, f)` vraćaju `false`.
