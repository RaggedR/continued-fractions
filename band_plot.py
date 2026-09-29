"""Panel A of period-distribution.pdf, redrawn."""
import numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import stats

d = np.load("data/band_300k_400k.npz"); n, L = d["n"], d["L"]
f = np.load("data/band_fits.npz")
t = L/np.sqrt(n)
es, ws, wc = float(f["exp_scale"]), float(f["wb_shape"]), float(f["wb_scale"])

fig, ax = plt.subplots(figsize=(11, 4.4))
ax.hist(t, bins=np.linspace(0, 2.6, 105), density=True,
        color="#cfd8de", edgecolor="#9fb0ba", linewidth=.3, label="the data")
x = np.linspace(1e-4, 2.6, 800)
ax.plot(x, stats.expon.pdf(x, 0, es), color="#c1443c", lw=1.9,
        label=f"exponential, mean {es:.3f}")
ax.plot(x, stats.weibull_min.pdf(x, ws, 0, wc), color="#2f6f8f", lw=1.9, ls="--",
        label=f"Weibull, shape {ws:.3f}")
ax.set_xlim(0, 2.6); ax.set_ylim(0, 4)
ax.set_xlabel(r"$L(n)/\sqrt{n}$"); ax.set_ylabel("density")
ax.set_title("A. An exponential gets the shape almost exactly", fontsize=11, loc="left")
fig.text(.5, .955, r"all 99,915 non-squares with $n$ between 300,000 and 400,000",
         ha="center", fontsize=9, color="#555")
ax.legend(frameon=False)
ax.text(.985, .60, f"KS  exponential {float(f['ks_e']):.4f}\n"
                   f"KS  Weibull      {float(f['ks_w']):.4f}\n"
                   f"5% cut            {float(f['crit']):.4f}\n"
                   "both rejected",
        transform=ax.transAxes, ha="right", va="top", fontsize=8.5, color="#444",
        family="monospace")
fig.tight_layout(rect=[0,0,1,.93])
fig.savefig("period-distribution-A.pdf")
print("wrote period-distribution-A.pdf")
