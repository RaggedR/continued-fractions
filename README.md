# continued-fractions

The period of the continued fraction of √n, recomputed from scratch, and the
question of what distribution L(n)/√n actually has.

## Why this exists

The figures in `~/git/education/fractions/` (14 September 2026) were written
without a generating script. `period-histogram.pdf`, `period-distribution.pdf`
and `learned-curve.pdf` are all orphaned from the code that produced them, and
`learned-curve.pdf` is fitted model output, so its numbers cannot be
reproduced or extended at all. This repository recomputes the first of those
figures with the source kept.

## Contents

| File | What it is |
|---|---|
| `period.py` | PQa recurrence: period L(n) and regulator R(n) for n < 10⁵. Validates R against three fundamental units known in closed form. |
| `analyse.py` | The decomposition L/√n = (L/R)·(R/√n), hazard rate, parity, mean growth. |
| `plots.py` | Redraws the comb histogram, 2 pages and 8 panels. |
| `band.py` | The n ∈ [300k, 400k) band: periods, exponential and Weibull fits, KS tests. |
| `band_plot.py` / `period-distribution-A.pdf` | Panel A of `period-distribution.pdf`, redrawn. |
| `method.tex` / `.pdf` | **Start here.** How it was computed, and what distribution L(n)/√n has. |
| `matrices.py` / `matrices.tex` / `.pdf` | The whole theory as Möbius transformations. M(a) = Tᵃ·J, so [1,1;0,1] is the alphabet; the trichotomy hyperbolic / parabolic / elliptic by tr²−4det; tr(period word) = 2x = 2cosh R or 2sinh R by the parity of L; the palindrome as conjugacy to the transpose; and where the Lévy shortfall in `analyse.py` comes from. |
| `musings.tex` / `.pdf` | Robin Langer, 14 September 2026. The companion piece this work extends — Archimedes → continued fractions → Pell → Sturmian. Also lives in `~/git/stream/`. |
| `data/periods.npz` | n, L(n), R(n) for all 99,683 non-squares below 10⁵. |
| `period-histogram.pdf` | The recomputed figure — 2 pages, 8 panels. |
| `distribution.pdf` | Two disjoint bands of n plotted together, showing the law drifts. |
| `lean/` | **The Lean 4 formalisation**, five files, 3,893 lines, no sorries, 51 theorems verified by `#print axioms`. See `lean/README.md` and `lean/PLAN.md`. |
| `sturmian.tex` / `.pdf` | The Sturmian side: codings of an irrational rotation, derived sequences, and the tower of derivations of √n. Assertion-dense — written to be checked, and it was. |
| `all-the-proofs.tex` / `.pdf` | Proofs of everything `sturmian.tex` asserts, plus the corrections it needed. This is what `lean/Sturmian.lean` and `lean/Lagrange.lean` formalise. |
| `step5_check.py` | The numerics behind `all-the-proofs.tex` §7, asserting rather than printing: the factor bound over 3,022,668 factors, the block decomposition, and the recovery of the intercept as `x = sup_N (S(N) − Nα)`. |
| `papers/` | Scans of Euler 1767, Lagrange 1770 and Legendre 1798, with an article-level index of where each theorem actually is. |
| `original/` | The 14 September originals, for comparison: `period-histogram.pdf`, `period-distribution.pdf`, and the `period-histogram.txt` write-up. Kept unmodified. |

`all-the-proofs.tex` is complete: §6 step 5, the last gap, is proved in §7
(3 October 2026). `HANDOVER.md` is the brief for what is left, which is Lean
Phase 9 — formalising §6 and §7.

## The Lean formalisation

Five files in `lean/`. `Palindrome`, `Lagrange` and `Sturmian` are mutually
independent; `Quadratic` imports `Palindrome`, and `SqrtN` imports the other
three:

| file | lines | contents |
|---|---|---|
| `Palindrome.lean` | 953 | Legendre's palindrome theorem for √n: Lagrange periodicity, the palindrome, `a_L = 2a₀`, the matrix side, and the bridge to Mathlib's `GenContFract`. |
| `Sturmian.lean` | 2057 | `all-the-proofs.tex` §§1–8: codings, density, complexity, gaps, the derivation theorem, Morse–Hedlund, the tower, the substitution. |
| `Lagrange.lean` | 212 | §9: Euler's half of Lagrange's theorem — eventually periodic ⟹ quadratic irrational. |
| `Quadratic.lean` | 544 | §9: Lagrange's half — every quadratic irrational has an eventually periodic continued fraction. Generalises `Palindrome.lean` off `Q = 1`. |
| `SqrtN.lean` | 127 | The √n instances of the tower and of Euler, joining the files. |

Two headline theorems beyond the classical ones:

* `sqrt_tower_period` — for every non-square `n`, deriving the Sturmian
  sequence of slope √n − ⌊√n⌋ exactly `L` times returns it with its first
  letter removed, `L` the period of the continued fraction. `sturmian.tex`
  observes this for `n = 2` and `n = 7`; here it holds for every `n`.
* `fib_sturmian_not_code` — a **refutation**. `sturmian.tex` §2 asserts every
  Sturmian sequence is a lower mechanical coding. The Fibonacci sequence with a
  `1` prefixed is Sturmian and is a lower coding of nothing. Both halves are
  proved in Lean.

Both halves of Lagrange's theorem are now formalised — Euler's 1737 direction
in `Lagrange.lean`, Lagrange's own 1770 direction in `Quadratic.lean`. Mathlib
has neither, nor a quadratic-irrational predicate, nor factor complexity, so
none of this was transcription.

## Reproducing

```bash
python3 period.py     # ~1 min, writes data/periods.npz
python3 analyse.py
python3 plots.py
tectonic method.tex
lean/build.sh         # ~3 min, checks all four Lean files and prints the axiom report
```

Needs numpy, matplotlib, tectonic.

## The result in one line

L(n)/√n is not a fixed distribution. It is roughly exponential with rate ≈2.1
through the bulk, has a lighter-than-exponential tail beyond t ≈ 1.4, and it
drifts with n — which is why the fit in `learned-curve.pdf` failed to transfer
between bands.

Part of that drift is now accounted for: the palindrome forces the last partial
quotient of every period to be 2a₀ ≈ 2√n, which inflates R by log(2a₀)/L ~
log n/√n. Removing that one term moves R/L from 1.33 to 1.21 on n ∈ [10⁵,10⁶),
against the Lévy prediction 1.187. See `matrices.tex` §7.

## Validation

Against `original/period-histogram.pdf` and its write-up:

| | September | recomputed |
|---|---|---|
| non-squares | 99,683 | 99,683 |
| shortest / longest period | 1 / 750 | 1 / 750 |
| mean / median | 77.84 / 48 | 77.84 / 48 |
| L > 40 | 54,889 | 54,889 |
| all 40 individual bars | — | identical |
| odd period | 11.52% | 11.52% |
| max L(n)/√n | 2.493 | 2.4932 |
| log-log slope (panel 6) | 0.431 | 0.4303 |
| odd period AND a prime factor 3 mod 4 | 0 | 0 |

Against `original/period-distribution.pdf`, on the band n ∈ [300,000, 400,000):

| | September | recomputed |
|---|---|---|
| non-squares in band | 99,915 | 99,915 |
| mean L(n)/√n | 0.334 | 0.3343 |
| Weibull shape | 0.948 | 0.9480 |
| KS distance, exponential | 0.0346 | 0.0346 |
| KS distance, Weibull | 0.0210 | 0.0210 |
| 5% critical value | 0.0043 | 0.0043 |

The regulators are checked independently against the fundamental units of 2, 13
and 61, agreeing to nine decimal places.
