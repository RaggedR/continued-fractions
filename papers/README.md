# Sources

Scans of the original papers behind the two theorems in `../palindrome.tex`.
All are public domain. Downloaded 2 October 2026.

**Two files here are not tracked by git** — `lagrange-oeuvres-t2.pdf` (27MB) and
`legendre-1798-essai.pdf` (26MB), the two full volumes. Together they are five
times the size of the rest of the repository. Everything needed to *find* a
result is tracked: this index, the four section excerpts, and both OCR text
layers. Re-download the full volumes from the bibliographic details below if you
need to look at a scan page outside the excerpts.

## Files

| File | What it is |
|---|---|
| `lagrange-oeuvres-t2.pdf` | *Œuvres de Lagrange*, tome 2 (Gauthier-Villars, 1868), full volume, 744 scan pages. Has a text layer. **Not tracked.** |
| `lagrange-1770-additions.pdf` | Excerpt: "Additions au mémoire sur la résolution des équations numériques", printed pp. 581–652. |
| `lagrange-oeuvres-t2-ocr.txt` | OCR text of the full volume (searchable). |
| `legendre-1798-essai.pdf` | Legendre, *Essai sur la théorie des nombres*, Paris: Duprat, an VI (1798), 1st edition, full volume, 562 scan pages. **No text layer** — use the OCR file to search. **Not tracked.** |
| `legendre-1798-S1-fractions-continues.pdf` | Excerpt: § I "Des fractions continues", printed pp. 21–34. |
| `legendre-1798-S5-racine-non-quarree.pdf` | Excerpt: § V "Développement de la racine d'un nombre non quarré en fraction continue", printed pp. 50–57. |
| `legendre-1798-S10-deux-racines.pdf` | Excerpt: § X "Comparaison des fractions continues ... des deux racines d'une même équation du second degré", printed pp. 90–98. |
| `legendre-1798-essai-ocr.txt` | OCR text of the full volume (searchable). |
| `euler-1767-E323-pellian.pdf` | Euler, "De usu novi algorithmi in problemate Pelliano solvendo", *Novi Comm. acad. sci. Petropolitanae* **11** (1767), pp. 29–66. The prior observation Lagrange credits and says was never proved. |

## Page offsets (printed page -> PDF scan page)

* `lagrange-oeuvres-t2.pdf`: add 10.
* `legendre-1798-essai.pdf`: add 28.

## Where the theorems are

**Theorem 1 (Lagrange, periodicity).** *Additions* (1770), Part II "Sur la manière
d'approcher de la valeur numérique des racines des équations", pp. 593–652.

* art. 19, p. 593 — "Remarque I. Sur les fractions continues périodiques".
* arts. 32–33, pp. 603–605 — "Remarque II. Où l'on donne une manière très-simple
  de réduire en fractions continues les racines des équations du second degré".
  This is the general-discriminant form of Lemma `pq`.
* art. 34, p. 606 — statement: "je dis que la fraction continue qui exprime la
  valeur de x sera toujours nécessairement périodique."
* arts. 35–38, pp. 607–611 — the finiteness bounds.
* art. 39, pp. 611–613 — backward determinacy (our Lemma `back`).
* arts. 40–42, pp. 613–615 — pure periodicity; art. 42 is the sqrt case.
* art. 43, p. 615 — priority: the converse "had long been remarked"; Euler
  observed the sqrt case without proving it.

**Theorem 2 (Legendre, palindrome).** *Essai* (1798), Première partie.

* arts. 10–11, pp. 30–31 — "Des fractions continues symmétriques": reversing a
  finite continued fraction reverses its quotients; symmetric iff q'' = p.
* art. 28, pp. 50–51 — worked example, sqrt(19) = [4; 2,1,3,1,2,8].
* art. 29, p. 52 — complete quotients are (sqrt(A)+I)/D with
  I' = mu*D - I, D' = (A - I'^2)/D. Our Lemma `pq`.
* art. 30, pp. 53–54 — the bounds 0 < I < sqrt(A), sqrt(A) - I < D < sqrt(A) + I,
  and finiteness. Our Lemma `finite`.
* art. 31, pp. 54–55 — the period begins at the first quotient after a_0.
* art. 32, pp. 55–56 — mu = 2a and the palindrome:
  "il faut que la période a, b, ... t, a soit identique avec son inverse",
  giving the law a; alpha,...,alpha, 2a, alpha,...,alpha, 2a, &c.
* art. 33, pp. 56–57 — p^2 - Aq^2 = +-1 at the quotient 2a; Pell always solvable.
* arts. 34–35, pp. 58–59 — (p+q sqrt A)^m and its conjugate multiplied give
  x^2 - Ay^2 = (p^2 - Aq^2)^m: multiplicativity of the norm, unnamed.
* art. 66, pp. 97–98 — general quadratic: the two roots have reversed periods.
