## 03 Cajtinova transformacija i čist literal

Rok za predaju:  *15.4.2022* \
Naslov mejla:    *[AR] Domaći zadatak 04_logika_prvog_reda* \
U prilogu mejla: *.cpp datoteka sa implementacijom rešenja*

Kod sa sedmog tročasa vežbi proširiti narednim funkcionalnostima.

1. Implementirati funkciju `bool hasQuantifier(FormulaPtr formula)` kojom se
ispituje da li formula sadrži bar jedan kvantifikator.
1. Implementirati funkciju `bool isPrenex(FormulaPtr formula)` kojom se
	ispituje da li je data formula u preneks normalnoj formi. Koristiti pomoćnu
	funkciju `hasQuantifier`.
1. U `main` funkciji programa definisati formule `Ax Ey p(x, f(y))` i `Ax (p(x)
	& Ey q(x, y))` i za obe ispitati da li su u preneks normalnoj formi.
