"""
Fit a Weibull to the density of L(n)/sqrt(n) on a sequence of bands of n.

For each band: the period of every non-square, the normalised variable
t = L(n)/sqrt(n), maximum-likelihood fits of the exponential and the Weibull
with location fixed at 0, Kolmogorov-Smirnov distances for both, and the
empirical hazard rate f(t)/P(X>t) on a fixed grid.
"""
import math, time, json, numpy as np
from scipy import stats
from period import period_and_regulator

BANDS = [(10_000, 40_000), (50_000, 80_000), (100_000, 130_000),
         (200_000, 230_000), (300_000, 400_000),
         (500_000, 530_000), (900_000, 930_000)]

EDGES = np.linspace(0, 2.4, 25)

def band(lo, hi):
    ts = []
    for n in range(lo, hi):
        a0 = math.isqrt(n)
        if a0*a0 == n: continue
        L, _ = period_and_regulator(n, a0)
        ts.append(L/math.sqrt(n))
    return np.array(ts)

rows, curves = [], {}
for lo, hi in BANDS:
    t0 = time.time(); t = band(lo, hi); el = time.time()-t0
    es = t.mean()
    k, _, sc = stats.weibull_min.fit(t, floc=0)
    ks_e = stats.kstest(t, "expon", args=(0, es)).statistic
    ks_w = stats.kstest(t, "weibull_min", args=(k, 0, sc)).statistic
    crit = 1.358/math.sqrt(len(t))
    h, _ = np.histogram(t, bins=EDGES)
    surv = len(t) - np.concatenate(([0], np.cumsum(h)))[:-1]
    w = EDGES[1]-EDGES[0]
    hz = np.where(surv > 50, h/np.maximum(surv,1)/w, np.nan)
    rows.append(dict(lo=lo, hi=hi, count=len(t), mean=es, k=k, scale=sc,
                     ks_e=ks_e, ks_w=ks_w, crit=crit, maxt=t.max(),
                     hmin=float(np.nanmin(hz)), hmax_tail=float(np.nanmax(hz[12:])),
                     secs=el))
    curves[f"{lo}"] = hz
    np.save(f"data/t_{lo}.npy", t)
    print(f"[{lo:>7,},{hi:>7,})  N={len(t):>6,}  mean {es:.4f}  k {k:.4f}"
          f"  KS_exp {ks_e:.4f}  KS_wb {ks_w:.4f}  crit {crit:.4f}  ({el:.0f}s)")

json.dump(rows, open("data/weibull_sweep.json","w"), indent=1)
np.savez("data/hazards.npz", edges=EDGES, **curves)
print("\nDRIFT")
for r in rows:
    print(f"  n~{r['lo']:>7,}   mean {r['mean']:.4f}   k {r['k']:.4f}"
          f"   max t {r['maxt']:.3f}   KS_wb/crit {r['ks_w']/r['crit']:5.1f}x")
