import json, math, numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

c = json.load(open("data/cumulative.json")); rows=c["rows"]
M = np.array([r["M"] for r in rows], float)
K = np.array([r["k"] for r in rows]); KS=np.array([r["ks"] for r in rows])
CR= np.array([r["crit"] for r in rows]); MU=np.array([r["mean"] for r in rows])
a,b = c["a"], c["b"]
ba, bb = -0.02897, 1.3197                      # band-wise fit, for comparison

fig, ax = plt.subplots(1, 3, figsize=(13.5, 4.2))

ax[0].semilogx(M, K, "o-", color="#2f6f8f", lw=1.7, ms=5, label="cumulative, $n<M$")
xx = np.logspace(3.4, 6.1, 50)
ax[0].semilogx(xx, b+a*np.log(xx), color="#2f6f8f", ls=":", lw=1.1,
               label=f"$k={b:.3f}{a:+.4f}\\log M$")
ax[0].semilogx(xx, bb+ba*np.log(xx), color="#3f8f5f", ls="--", lw=1.4,
               label="band-wise, for comparison")
ax[0].axhline(1, color="#c1443c", lw=1.2)
ax[0].axvline(math.exp((1-b)/a), color="#c1443c", lw=.8, ls="--")
ax[0].annotate(f"crosses at $M\\approx{math.exp((1-b)/a):,.0f}$".replace(",","{,}"),
               (math.exp((1-b)/a),1.0), textcoords="offset points", xytext=(-6,12),
               fontsize=8, color="#c1443c", ha="right")
ax[0].set_xlabel("$M$"); ax[0].set_ylabel("fitted Weibull shape $k$")
ax[0].set_title("A. $k$ falls linearly in $\\log M$", fontsize=10, loc="left")
ax[0].legend(frameon=False, fontsize=7.5)

ax[1].loglog(M, KS, "o-", color="#2f6f8f", lw=1.7, ms=5, label="KS distance")
ax[1].loglog(M, CR, "s--", color="#c1443c", lw=1.4, ms=4, label="5% critical value")
ax[1].set_xlabel("$M$"); ax[1].set_ylabel("KS")
ax[1].set_title("B. The misfit holds still; the test sharpens", fontsize=10, loc="left")
ax[1].legend(frameon=False, fontsize=8)

ax[2].semilogx(M, KS/CR, "o-", color="#c1443c", lw=1.7, ms=5)
ax[2].axhline(1, color="#888", lw=1, ls=":")
ax[2].set_xlabel("$M$"); ax[2].set_ylabel("KS / critical value")
ax[2].set_title("C. Rejection grows like $\\sqrt{M}$", fontsize=10, loc="left")

fig.tight_layout(); fig.savefig("cumulative-figure.pdf")
print(f"k = {b:.4f} {a:+.5f} log M    crosses 1 at M = {math.exp((1-b)/a):,.0f}")
print(f"KS/crit:  {KS[0]/CR[0]:.1f}x at M={M[0]:,.0f}   ->   {KS[-1]/CR[-1]:.1f}x at M={M[-1]:,.0f}")
