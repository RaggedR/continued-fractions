"""Figures for alogos.tex: densities at four smallish M, and k against M."""
import math, numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import stats
from wfit import weibull_mle

d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
t_all = L/np.sqrt(n)

# ---- densities at four smallish ceilings -------------------------------
MS = [1_000, 3_000, 10_000, 30_000]
fig, axes = plt.subplots(2, 2, figsize=(10.5, 7.0), sharex=True, sharey=True)
bins = np.linspace(0, 2.6, 46); x = np.linspace(1e-4, 2.6, 600)
for ax, M in zip(axes.ravel(), MS):
    t = t_all[n < M]
    k, sc = weibull_mle(t)
    ax.hist(t, bins=bins, density=True, color="#d5dde2", edgecolor="#9fb0ba", lw=.3)
    ax.plot(x, stats.weibull_min.pdf(x, k, 0, sc), color="#2f6f8f", lw=2)
    ax.set_title(f"$M = {M:,}$".replace(",", "{,}") +
                 f"    ({len(t):,} values of $n$)".replace(",", "{,}"), fontsize=10)
    ax.text(.96, .86, f"$k = {k:.3f}$", transform=ax.transAxes, ha="right", fontsize=17)
    ax.set_xlim(0, 2.6); ax.set_ylim(0, 3.0)
    print(f"  M={M:>7,}  N={len(t):>7,}  k={k:.4f}  scale={sc:.4f}")
for ax in axes[1]: ax.set_xlabel(r"$L(n)/\sqrt{n}$")
for ax in axes[:,0]: ax.set_ylabel("density")
fig.tight_layout(); fig.savefig("alogos-densities.pdf")

# ---- k against M, plain ------------------------------------------------
Ms = np.unique(np.round(np.logspace(3, 6, 40)).astype(np.int64))
ks = np.array([weibull_mle(t_all[n < M], it=45)[0] for M in Ms])
fig, ax = plt.subplots(figsize=(9, 5.4))
ax.semilogx(Ms, ks, "o-", color="#2f6f8f", lw=1.8, ms=5)
ax.set_xlabel("$M$"); ax.set_ylabel("$k$")
fig.tight_layout(); fig.savefig("alogos-k-vs-M.pdf")
print(f"  k: {ks[0]:.4f} at M={Ms[0]:,}  ->  {ks[-1]:.4f} at M={Ms[-1]:,}")
