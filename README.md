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
| `plots.py` | Redraws the comb histogram and the density. |
| `method.tex` / `.pdf` | **Start here.** How it was computed, and what distribution L(n)/√n has. |
| `musings.tex` / `.pdf` | Robin Langer, 14 September 2026. The companion piece this work extends — Archimedes → continued fractions → Pell → Sturmian. Also lives in `~/git/stream/`. |
| `data/periods.npz` | n, L(n), R(n) for all 99,683 non-squares below 10⁵. |

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

## Validation

The recomputed histogram reproduces the September figures exactly: 99,683
non-squares, shortest period 1, longest 750, mean 77.84, median 48, and 54,889
with L > 40.
