# Sturmian sources

For the one target left in `../../lean/PLAN.md`: the converse half of
Morse–Hedlund (`all-the-proofs.tex` §6, steps 2, 4a and 5).

All three are **freely offered by their authors**, unlike the two originals,
which are not available:

* **Morse, M. and Hedlund, G. A.**, "Symbolic Dynamics II. Sturmian
  Trajectories", *American Journal of Mathematics* **62** (1940), 1–42. The
  original. Paywalled (JSTOR / Project MUSE), and in copyright until 2035.
* **M. Lothaire**, *Algebraic Combinatorics on Words*, CUP 2002, **Chapter 2
  "Sturmian Words" by Jean Berstel and Patrice Séébold**. Where the proof
  actually is. Berstel's Lothaire page posts only the contents, solutions and
  errata for this volume — no chapter PDFs. (It does post chapter 1 of the
  *1983* volume, which is a different book.)

| File | What it is | What it gives us |
|---|---|---|
| `berstel-2003-tutorial.pdf` | J. Berstel, "Combinatorics on Words" tutorial, 53pp | **Statement only.** Theorem 6.5 is the three-way equivalence, cited to [MH40], with "A proof can be found in Chapter 2 of [Lot02]". Valuable anyway: its definitions are *exactly* ours (`s_{α,ρ}(n) = ⌊α(n+1)+ρ⌋ − ⌊αn+ρ⌋`, and the rotation partition `I₀ = [0,1−α)`, `I₁ = [1−α,1)`), and it gives the standard-sequence recurrence `sₙ = sₙ₋₁^{dₙ} sₙ₋₂` with `[0; 1+d₁, d₂, …]` the continued fraction of the slope. |
| `berstel-2007-survey.pdf` | J. Berstel, "Sturmian and Episturmian Words (A Survey of Some Recent Results)", 8pp | Orientation. Also statement-only. |
| `berstel-lauve-reutenauer-saliola-christoffel.pdf` | J. Berstel, A. Lauve, C. Reutenauer, F. Saliola, *Combinatorics on Words: Christoffel Words and Repetitions in Words*, CRM monograph, 202pp | **The finite theory in full.** Balanced finite words are exactly the factors of Christoffel words (§6.2); a Lyndon word is Christoffel iff `xux, xuy, yux, yuy` are all balanced — the same `0w0`/`1w1` structure §6 step 2 needs; palindromic characterisation (ch. 4); continued fractions and Christoffel words (§7); Stern–Brocot (§7.3). Defers the infinite Sturmian theory to [Lot2002, Ch. 2]. |

## Not found

No freely available source carries the *infinite* step — balanced and aperiodic
⟹ mechanical — in full. Searched author homepages, arXiv and open-access
journals; the open literature consistently states it and cites Lothaire ch. 2.
If a copy of that chapter turns up, it supersedes all three files here for
planning purposes.
