"""
Panel A of period-distribution.pdf: the density of L(n)/sqrt(n) for
n in [300000, 400000), with an exponential and a Weibull fitted to it.

Same PQa recurrence as period.py, run on a higher band.  About 1.4e7 steps.
"""
import math, numpy as np
from period import period_and_regulator

LO, HI = 300_000, 400_000
ns, Ls = [], []
for n in range(LO, HI):
    a0 = math.isqrt(n)
    if a0*a0 == n: continue
    L, _ = period_and_regulator(n, a0)
    ns.append(n); Ls.append(L)
n = np.array(ns, dtype=np.int64); L = np.array(Ls, dtype=np.int64)
t = L/np.sqrt(n)
np.savez_compressed("data/band_300k_400k.npz", n=n, L=L)

print(f"n in [{LO:,}, {HI:,}):  {len(n):,} non-squares")
print(f"  mean L        {L.mean():.2f}    longest {L.max()}")
print(f"  mean L/sqrt(n) {t.mean():.4f}   (September: 0.334)")

from scipy import stats
exp_scale = t.mean()
wb_shape, _, wb_scale = stats.weibull_min.fit(t, floc=0)
print(f"  exponential mean  {exp_scale:.4f}")
print(f"  Weibull shape     {wb_shape:.4f}   (September: 0.948)")
ks_e = stats.kstest(t, "expon", args=(0, exp_scale)).statistic
ks_w = stats.kstest(t, "weibull_min", args=(wb_shape, 0, wb_scale)).statistic
crit = 1.358/math.sqrt(len(t))
print(f"  KS exponential {ks_e:.4f}  (September: 0.0346)")
print(f"  KS Weibull     {ks_w:.4f}  (September: 0.0210)")
print(f"  5% critical value {crit:.4f} -> both rejected: {ks_e>crit and ks_w>crit}")
np.savez("data/band_fits.npz", exp_scale=exp_scale, wb_shape=wb_shape, wb_scale=wb_scale,
         ks_e=ks_e, ks_w=ks_w, crit=crit)
