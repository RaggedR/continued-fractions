"""Panel A of period-distribution.pdf, redrawn with the exponential only."""
import numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import stats

d = np.load("data/band_300k_400k.npz"); n, L = d["n"], d["L"]
f = np.load("data/band_fits.npz")
t = L/np.sqrt(n)
es = float(f["exp_scale"])

fig, ax = plt.subplots(figsize=(11, 4.4))
ax.hist(t, bins=np.linspace(0, 2.6, 105), density=True,
        color="#cfd8de", edgecolor="#9fb0ba", linewidth=.3, label="the data")
x = np.linspace(1e-4, 2.6, 800)
ax.plot(x, stats.expon.pdf(x, 0, es), color="#c1443c", lw=1.9,
        label=f"exponential, mean {es:.3f}")
ax.set_xlim(0, 2.6); ax.set_ylim(0, 4)
ax.set_xlabel(r"$L(n)/\sqrt{n}$"); ax.set_ylabel("density")
ax.set_title("The exponential distribution doesn't quite fit.", fontsize=11, loc="left")
fig.text(.5, .955, r"all 99,915 non-squares with $n$ between 300,000 and 400,000",
         ha="center", fontsize=9, color="#555")
ax.legend(frameon=False)
fig.tight_layout(rect=[0,0,1,.93])
fig.savefig("period-distribution-A-exp.pdf")
print("wrote period-distribution-A-exp.pdf")
