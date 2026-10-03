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
| `lean/Palindrome.lean` | **Legendre's theorem, formalised in Lean 4.** 954 lines, no sorries, verified by `#print axioms`. Includes Lagrange periodicity, the palindrome, `a_L = 2a₀`, the matrix side, and the bridge to Mathlib's `GenContFract`. See `lean/README.md`. |
| `original/` | The 14 September originals, for comparison: `period-histogram.pdf`, `period-distribution.pdf`, and the `period-histogram.txt` write-up. Kept unmodified. |

## Reproducing

```bash
python3 period.py     # ~1 min, writes data/periods.npz
python3 analyse.py
python3 plots.py
tectonic method.tex
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
