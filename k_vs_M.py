"""k, the fitted Weibull shape, against M, the largest n included."""
import math, numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from wfit import weibull_mle

d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
t_all = L/np.sqrt(n)
Ms = np.unique(np.round(np.logspace(3, 6, 40)).astype(np.int64))
ks = np.array([weibull_mle(t_all[n < M], it=45)[0] for M in Ms])
x  = np.log(Ms)

lin      = np.polyfit(x, ks, 1)
pw, _    = curve_fit(lambda X,A,B,be: A+B*np.exp(-be*X), x, ks, p0=[.9,3,.3], maxfev=40000)
plg, _   = curve_fit(lambda X,A,B: A+B/X, x, ks, p0=[.5,5])
f_lin    = lambda X: lin[1]+lin[0]*X
f_pw     = lambda X: pw[0]+pw[1]*np.exp(-pw[2]*X)
f_lg     = lambda X: plg[0]+plg[1]/X
cross    = math.exp((math.log((1-pw[0])/pw[1]))/(-pw[2]))

fig, ax = plt.subplots(figsize=(10, 6))
ax.axhspan(1, 1.4, color="#3f8f5f", alpha=.05)
ax.axhspan(.5, 1, color="#8a4f9f", alpha=.05)
xx = np.linspace(math.log(900), math.log(2e7), 300); MM = np.exp(xx)

ax.semilogx(MM, f_lin(xx), color="#bbb", ls=":", lw=1.4,
            label=f"straight line in $\\log M$   (rms {np.std(ks-f_lin(x)):.4f})")
ax.semilogx(MM, f_lg(xx), color="#c9a227", ls="-.", lw=1.4,
            label=f"$A+B/\\log M$   $\\to{plg[0]:.3f}$   (rms {np.std(ks-f_lg(x)):.4f})")
ax.semilogx(MM, f_pw(xx), color="#2f6f8f", lw=1.7,
            label=f"$A+BM^{{-\\beta}}$, $\\beta={pw[2]:.3f}$   $\\to{pw[0]:.3f}$   (rms {np.std(ks-f_pw(x)):.4f})")
ax.semilogx(Ms, ks, "o", color="#123", ms=5.5, zorder=5, label="fitted $k(M)$")

ax.axhline(1, color="#c1443c", lw=1.4)
ax.axvline(cross, color="#c1443c", lw=.9, ls="--")
ax.plot([cross],[1],"o",ms=9,mfc="none",mec="#c1443c",mew=1.8, zorder=6)
ax.annotate(f"$k=1$, exactly the exponential\n$M\\approx{cross:,.0f}$".replace(",","{,}"),
            (cross,1), textcoords="offset points", xytext=(16,30), fontsize=9, color="#c1443c",
            arrowprops=dict(arrowstyle="-", color="#c1443c", lw=.8))
ax.axvspan(1e6, 2e7, color="#000", alpha=.04)
ax.text(3.2e6, 1.30, "beyond the data", fontsize=8, color="#999", ha="center")
ax.text(1.15e3, 1.315, "$k>1$  hazard rising", fontsize=9, color="#3f8f5f")
ax.text(1.15e3, 0.565, "$k<1$  hazard falling", fontsize=9, color="#8a4f9f")
ax.text(.5, .055, "The three curves agree on the data and disagree on the limit, from 0.56 to 0.86.\n"
                  "The measurement settles that $k$ decelerates; it does not settle where it stops.",
        transform=ax.transAxes, ha="center", fontsize=8.5, color="#555")

ax.set_xlabel("$M$,  the largest $n$ for which $L(n)/\\sqrt{n}$ is computed")
ax.set_ylabel("fitted Weibull shape  $k$")
ax.set_title("$k$ against $M$: it falls, it decelerates, and it does not stop inside the data", fontsize=12)
ax.set_xlim(1e3, 2e7); ax.set_ylim(.5, 1.4)
ax.legend(frameon=False, fontsize=8.5, loc="upper right")
fig.tight_layout(); fig.savefig("k-vs-M.pdf")
print(f"crossing k=1 at M = {cross:,.0f}")
print(f"limits:  power law {pw[0]:.4f}   1/log {plg[0]:.4f}")
print("wrote k-vs-M.pdf")
