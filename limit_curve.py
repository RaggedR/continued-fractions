"""
The large-M limit of the cumulative difference curve, and a real function for it.
"""
import numpy as np, math, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import stats

z = np.load("data/limit_curve.npz"); g, D, Dpred = z["g"], z["D"], z["Dpred"]
a, b, c, dd = z["p2"]
c2 = np.load("data/dcdf.npz")
fit = np.exp(-b*g)*(a*g + c*g**2 + dd*g**3)
roots = np.roots([dd, c, a]); roots = sorted(r.real for r in roots if abs(r.imag) < 1e-9 and r.real > 0)

fig, ax = plt.subplots(1, 2, figsize=(13.5, 5))
C = plt.cm.viridis(np.linspace(.1, .8, 5))
for (M, col) in zip([30_000, 100_000, 300_000, 600_000, 1_000_000], C):
    ax[0].plot(c2["g"], c2[str(M)], color=col, lw=1.4, label=f"$M={M:,}$".replace(",", "{,}"))
ax[0].axhline(0, color="#999", lw=.9)
ax[0].set_xlim(0, 2.8); ax[0].set_xlabel("$t$")
ax[0].set_ylabel("empirical $-$ fitted, cumulative")
ax[0].set_title("A. The curve settles as $M$ grows", fontsize=11, loc="left")
ax[0].legend(frameon=False, fontsize=8)

ax[1].plot(g, D, color="#123", lw=2.4, label="$D(t)$ at $M=10^6$")
ax[1].plot(g, fit, color="#c1443c", lw=1.6, ls="--",
           label=r"$e^{-bt}(at+ct^2+dt^3)$, rms $0.0016$")
ax[1].plot(g, Dpred, color="#3f8f5f", lw=1.6, ls=":",
           label="predicted by a two-component mixture")
ax[1].axhline(0, color="#999", lw=.9)
for r in roots[:2]:
    ax[1].plot([r], [0], "o", ms=6, mfc="none", mec="#c1443c", mew=1.5)
ax[1].set_xlim(0, 2.8); ax[1].set_xlabel("$t$"); ax[1].set_ylabel("$D(t)$")
ax[1].set_title("B. Two approximations to the limit", fontsize=11, loc="left")
ax[1].legend(frameon=False, fontsize=8.5)
fig.tight_layout(); fig.savefig("limit-curve.pdf")
print(f"D(t) ~ e^(-{b:.3f} t) ( {a:+.4f} t {c:+.4f} t^2 {dd:+.4f} t^3 )")
print(f"  its positive roots: {roots[0]:.3f}, {roots[1]:.3f}"
      f"   (observed sign changes 0.083 and 0.64)")
