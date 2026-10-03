# Sturmian sources

For the one target left in `../../lean/PLAN.md`: Phase 9, the converse half of
Morse–Hedlund. Steps 2 and 4 of `all-the-proofs.tex` §6 were proved on
3 October 2026, and **step 5 later the same day** — it is §7 of that document.
The proof needs none of the sources below: see `../../HANDOVER.md`.

## The two that could not be obtained

* **Morse, M. and Hedlund, G. A.**, "Symbolic Dynamics II. Sturmian
  Trajectories", *American Journal of Mathematics* **62** (1940), no. 1, 1–42.
  The original. Paywalled (JSTOR / Project MUSE) and in copyright until 2035.
* **M. Lothaire**, *Algebraic Combinatorics on Words*, CUP 2002, **Chapter 2
  "Sturmian Words", by Jean Berstel and Patrice Séébold**. Where the proof
  actually is; the equivalence is Theorem 2.1.13. Berstel's Lothaire page posts
  only the contents, errata and chapter-1 solutions for this volume — no
  chapter PDFs, and the chapter-2 solutions are listed but not linked. (The one
  full-text chapter there belongs to the *1983* volume, a different book.)

If either turns up it supersedes everything below for planning purposes.

## What is here

| File | What it is | What it gives |
|---|---|---|
| `berstel-2003-tutorial.pdf` | J. Berstel, "Combinatorics on Words" tutorial, 53pp | **Statement only** (Thm 6.5, cited to [MH40], proof deferred to [Lot02] ch. 2). Valuable regardless: its definitions are *verbatim* ours — `s_{α,ρ}(n) = ⌊α(n+1)+ρ⌋ − ⌊αn+ρ⌋` is our `code_eq_sub_floor`, and the rotation partition `I₀ = [0,1−α)`, `I₁ = [1−α,1)` is our `code`. Also gives the standard-sequence recurrence `sₙ = sₙ₋₁^{dₙ} sₙ₋₂` with `[0; 1+d₁, d₂, …]` the slope's continued fraction. |
| `berstel-lauve-reutenauer-saliola-christoffel.pdf` | Berstel, Lauve, Reutenauer, Saliola, *Combinatorics on Words: Christoffel Words and Repetitions in Words*, CRM monograph, 202pp | **The finite theory in full.** Balanced finite words are exactly the factors of Christoffel words (§6.2); a Lyndon word is Christoffel iff `xux, xuy, yux, yuy` are all balanced — the same `0w0`/`1w1` structure step 2 needs; palindromic characterisation (ch. 4); continued fractions and Christoffel words (§7); Stern–Brocot (§7.3). Defers the infinite theory to [Lot2002, ch. 2]. **Best starting point available for step 2**, whose induction lives in the finite setting. |
| `lothaire-ACW-errata.pdf` | Errata to *Algebraic Combinatorics on Words*, 2pp | Small but **the most informative thing here about ch. 2's structure.** The Sturmian entries sit on pp. 56–61, and the correction to Proposition 2.1.18 quotes its proof: *"We may suppose that β < α. For any factor u of s such that (α−β) ≥ 2/\|u\|, one has π(u)−α > −1/\|u\| by Proposition 2.1.10 …"*. So `π(u)` is the frequency of `1`s in a factor, **Prop. 2.1.10 is a quantitative bound `\|π(u)·\|u\| − α·\|u\|\| < 1`**, and 2.1.18 uses it to show two candidate slopes coincide. That bound is the converse of our `sum_code`, and it is step 5's machinery. Also: anything transcribed from ch. 2 must be checked against this file. |
| `glen-justin-episturmian-survey.pdf` | A. Glen and J. Justin, "Episturmian words: a survey", arXiv:0801.1655, 36pp | States the equivalence as well known (§1) without proof, but carries the **directive-word / epistandard machinery with proofs** (Thm 2.3), and notes that in the binary case the directive word is related to the continued fraction — the generalisation of the standard-sequence recurrence, hence relevant to step 5. |
| `berstel-2007-survey.pdf` | J. Berstel, "Sturmian and Episturmian Words (A Survey of Some Recent Results)", 8pp | Orientation. Statement only. |
| `lothaire-ACW-contents.html` | Contents of the 2002 volume | Chapter titles and authors only — no section structure. Confirms ch. 2 is Berstel–Séébold. |
| `lothaire-ACW-solutions.html` | Solutions page | Chapter 1 only; the Sturmian entry is listed but unlinked. Kept so nobody re-checks. |
| `lothaire-bibliography.bib` | The book's bibliography, BibTeX | Citation precision for anything transcribed from it. |

All of the above are offered freely by their authors. This repository is
private; nothing here is redistributed.

## Known gap

**L. Vuillon, "Balanced words", *Bull. Belg. Math. Soc. Simon Stevin* 10 (2003),
no. 5, 787–805** (`doi:10.36045/bbms/1074791332`). The most on-point title for
step 2, and the journal is open access, but three download attempts failed —
Project Euclid's direct-PDF and `.full` routes and the author's old
`lama.univ-savoie.fr` page all returned HTML rather than a PDF. Worth one more
try from a different network, or via a library proxy.
