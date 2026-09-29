"""
Panel A of period-distribution.pdf, drawn for four values of M and annotated
with the fitted Weibull shape.  Cumulative samples: every non-square n < M.
"""
import math, numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import stats
from wfit import weibull_mle

d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
t_all = L/np.sqrt(n)
MS = [3_162, 10_000, 100_000, 1_000_000]

fig, axes = plt.subplots(2, 2, figsize=(11.7, 7.6), sharex=True, sharey=True)
fig.suptitle(r"What distribution is $L(n)/\sqrt{n}$ ?   —   the same picture at four ceilings $M$",
             fontsize=13, y=.975)
bins = np.linspace(0, 2.8, 80); x = np.linspace(1e-4, 2.8, 700)

for ax, M in zip(axes.ravel(), MS):
    t = t_all[n < M]
    k, sc = weibull_mle(t)
    mu = t.mean()
    ks = stats.kstest(t, "weibull_min", args=(k, 0, sc)).statistic
    crit = 1.358/math.sqrt(len(t))
    ax.hist(t, bins=bins, density=True, color="#cfd8de", edgecolor="#9fb0ba", lw=.25,
            label="the data")
    ax.plot(x, stats.expon.pdf(x, 0, mu), color="#c1443c", lw=1.7,
            label=f"exponential, mean {mu:.3f}")
    ax.plot(x, stats.weibull_min.pdf(x, k, 0, sc), color="#2f6f8f", lw=1.9, ls="--",
            label=f"Weibull, $k={k:.3f}$")
    ax.set_title(f"$M={M:,}$".replace(",", "{,}") + f"   ({len(t):,} non-squares)".replace(",", "{,}"),
                 fontsize=10, loc="left")
    col = "#3f8f5f" if k > 1 else "#8a4f9f"
    ax.text(.97, .82, f"$k={k:.3f}$", transform=ax.transAxes, ha="right",
            fontsize=19, color=col, weight="bold")
    ax.text(.97, .72, ("hazard rising" if k > 1 else "hazard falling"),
            transform=ax.transAxes, ha="right", fontsize=8.5, color=col)
    ax.text(.97, .64, f"KS {ks:.4f} vs cut {crit:.4f}  ({ks/crit:.1f}x)",
            transform=ax.transAxes, ha="right", fontsize=7.5, color="#666")
    ax.legend(frameon=False, fontsize=7.5, loc="upper right", bbox_to_anchor=(1.0, .62))
    ax.set_xlim(0, 2.8); ax.set_ylim(0, 3.6)

for ax in axes[1]: ax.set_xlabel(r"$L(n)/\sqrt{n}$")
for ax in axes[:,0]: ax.set_ylabel("density")
fig.text(.5, .015, r"$k=1$ is exactly the exponential.  The fitted shape falls through it near "
                   r"$M\approx196{,}000$: green above, purple below.",
         ha="center", fontsize=9, color="#444")
fig.tight_layout(rect=[0, .035, 1, .945])
fig.savefig("period-distribution-A-by-M.pdf")
print("wrote period-distribution-A-by-M.pdf")
for M in MS:
    t = t_all[n < M]; k, _ = weibull_mle(t)
    print(f"  M={M:>9,}  N={len(t):>8,}  mean {t.mean():.4f}  k {k:.4f}")
