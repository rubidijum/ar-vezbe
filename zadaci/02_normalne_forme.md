## 01 Dubina iskazne formule

Rok za predaju:  *17.3.2022* \
Naslov mejla:    *[AR] Domaći zadatak 02_normalne_forme* \
U prilogu mejla: *Sve potrebne .cpp i .h datoteke*

Kod sa drugog tročasa vežbi proširiti narednim funkcionalnostima.

1. Po uzoru na implementaciju funkcije `isSatisfiable` implementirati funkciju
`std::optional<Valuation> isFalsifiable(FormulaPtr formula)` koja ispituje da
li je formula poreciva (odnosno da li ima kontramodel) i ukoliko jeste vraća
jedan takav kontramodel.
1. Po uzoru na implementaciju funkcije `cnf` implementirati funkciju
`NormalForm dnf(FormulaPtr formula)` kojom se određuje disjunktivna normalna
forma date formule. Pretpostavlja se da je zadata formula već svedena na
negacionu normalnu formu.
1. U `main` funkciji programa definisati formulu `(p -> r) & (p | r)`. Ispitati njenu porecivost i na standardni izlaz ispisati rezultat i DNF zadate formule.
