## 05 Primena supstitucije na term

Rok za predaju:  *23.4.2022* \
Naslov mejla:    *[AR] Domaći zadatak 05_unifikacija* \
U prilogu mejla: *.cpp datoteka sa implementacijom rešenja*

Kod sa osmog tročasa vežbi proširiti narednim funkcionalnostima.

1. Po uzoru na postojeću implementaciju funkcije substitute za termove,
	implementirati funkciju `TermPtr substitute(TermPtr t, const Substitution& s)`
	kojom se određuje term dobijen primenom supstitucije `s` na term `t`.
1. Dopuniti `main` funkciju programa tako da se supstitucija `unifier` dobijena
unifikacijom primenjuje na term `f(x, y, z)` i ispisuje dobijeni term.
Očekivani ispis je `f(a, g(b), z)`.
