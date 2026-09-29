"""
Where the Weibull actually misses: the histogram minus the fitted density,
and the same difference in cumulative form, for several ceilings M.
"""
import math, numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import stats
from wfit import weibull_mle

d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
t_all = L/np.sqrt(n)
MS = [10_000, 31_623, 100_000, 316_228, 1_000_000]
E  = np.linspace(0, 2.8, 57); mid = (E[:-1]+E[1:])/2; w = E[1]-E[0]
C  = plt.cm.viridis(np.linspace(.05, .85, len(MS)))

fig, ax = plt.subplots(1, 2, figsize=(13.5, 4.8))
print(f"{'M':>10} {'N':>9} {'k':>7} {'max |dens resid|':>17} {'KS':>8} {'at t':>7}")
for M, c in zip(MS, C):
    t = t_all[n < M]; N = len(t)
    k, sc = weibull_mle(t)
    cnt, _ = np.histogram(t, bins=E)
    emp = cnt/(N*w)                                   # empirical density
    fit = np.diff(stats.weibull_min.cdf(E, k, 0, sc))/w   # fitted, same bins
    resid = emp - fit
    se = np.sqrt(np.maximum(cnt,1))/(N*w)             # 1 sigma on each bin
    ax[0].plot(mid, resid, color=c, lw=1.5, label=f"$M=10^{{{math.log10(M):.1f}}}$")
    if M == MS[-1]:
        ax[0].fill_between(mid, -2*se, 2*se, color="#999", alpha=.25, lw=0,
                           label=r"$\pm 2\sigma$ at $M=10^6$")
    Fe = np.searchsorted(np.sort(t), E)/N
    dcdf = Fe - stats.weibull_min.cdf(E, k, 0, sc)
    ax[1].plot(E, dcdf, color=c, lw=1.5)
    ks = np.abs(dcdf).max()
    print(f"{M:>10,} {N:>9,} {k:>7.4f} {np.abs(resid).max():>17.4f} {ks:>8.4f}"
          f" {E[np.abs(dcdf).argmax()]:>7.2f}")

ax[0].axhline(0, color="#c1443c", lw=1.1)
ax[0].set_xlabel(r"$t=L(n)/\sqrt{n}$"); ax[0].set_ylabel("histogram $-$ fitted density")
ax[0].set_title("A. Where the density misses", fontsize=11, loc="left")
ax[0].legend(frameon=False, fontsize=8)
ax[1].axhline(0, color="#c1443c", lw=1.1)
ax[1].set_xlabel("$t$"); ax[1].set_ylabel("empirical $-$ fitted, cumulative")
ax[1].set_title("B. The same difference, accumulated (its peak is the KS statistic)",
                fontsize=11, loc="left")
fig.tight_layout(); fig.savefig("residuals.pdf")
print("wrote residuals.pdf")
