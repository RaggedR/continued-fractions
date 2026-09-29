import json, math, numpy as np, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import stats

rows = json.load(open("data/weibull_sweep.json"))
hz   = np.load("data/hazards.npz"); E = hz["edges"]; mid=(E[:-1]+E[1:])/2
mids = [math.sqrt(r["lo"]*r["hi"]) for r in rows]
ks   = [r["k"] for r in rows]; mus=[r["mean"] for r in rows]

a, b = np.polyfit(np.log(mids), ks, 1)
cross = math.exp((1.0-b)/a)
am, bm = np.polyfit(np.log(mids), mus, 1)
print(f"k = {b:.4f} + {a:.5f} log n     crosses k=1 at n = {cross:,.0f}")
print(f"mean = {bm:.4f} + {am:.5f} log n")

fig = plt.figure(figsize=(11.7, 8.6))
C = plt.cm.viridis(np.linspace(.08,.88,len(rows)))

ax = fig.add_subplot(2,2,1)
for r,c in zip(rows,C):
    t = np.load(f"data/t_{r['lo']}.npy")
    h,e = np.histogram(t, bins=np.linspace(0,2.6,70), density=True)
    ax.plot((e[:-1]+e[1:])/2, h, color=c, lw=1.2, label=f"$n\\sim${r['lo']//1000}k")
ax.set_xlabel("$t=L(n)/\\sqrt{n}$"); ax.set_ylabel("density")
ax.set_title("A. The density, band by band", fontsize=10, loc="left")
ax.legend(frameon=False, fontsize=7, ncol=2)

ax = fig.add_subplot(2,2,2)
r = rows[4]; t = np.load(f"data/t_{r['lo']}.npy")
ax.hist(t, bins=np.linspace(0,2.6,90), density=True, color="#cfd8de", edgecolor="#9fb0ba", lw=.3)
x = np.linspace(1e-4,2.6,700)
ax.plot(x, stats.expon.pdf(x,0,r["mean"]), color="#c1443c", lw=1.8, label=f"exponential, mean {r['mean']:.3f}")
ax.plot(x, stats.weibull_min.pdf(x,r["k"],0,r["scale"]), color="#2f6f8f", lw=1.8, ls="--",
        label=f"Weibull, $k={r['k']:.3f}$")
ax.set_xlabel("$t$"); ax.set_ylabel("density"); ax.set_ylim(0,4)
ax.set_title(f"B. Both fits, $n\\in[300{{,}}000,400{{,}}000)$", fontsize=10, loc="left")
ax.legend(frameon=False, fontsize=8)

ax = fig.add_subplot(2,2,3)
ax.semilogx(mids, ks, "o-", color="#2f6f8f", lw=1.6, ms=5)
xx=np.logspace(3.9,6.1,50); ax.semilogx(xx, b+a*np.log(xx), color="#888", ls=":", lw=1.2,
        label=f"$k={b:.3f}{a:+.4f}\\log n$")
ax.axhline(1, color="#c1443c", lw=1.2, label="$k=1$, the exponential")
ax.axvline(cross, color="#c1443c", lw=.8, ls="--")
ax.annotate(f"crosses at $n\\approx{cross:,.0f}$".replace(",","{,}"), (cross,1.0),
            textcoords="offset points", xytext=(8,-22), fontsize=8, color="#c1443c")
ax.set_xlabel("$n$"); ax.set_ylabel("fitted Weibull shape $k$")
ax.set_title("C. The shape drifts through 1 and keeps going", fontsize=10, loc="left")
ax.legend(frameon=False, fontsize=8)

ax = fig.add_subplot(2,2,4)
for r,c in zip(rows,C):
    ax.plot(mid, hz[str(r["lo"])], color=c, lw=1.3)
r = rows[4]
ax.plot(mid, (r["k"]/r["scale"])*(mid/r["scale"])**(r["k"]-1), color="#c1443c", lw=2, ls="--",
        label=f"Weibull hazard, $k={r['k']:.3f}$ (monotone)")
ax.set_xlabel("$t$"); ax.set_ylabel("hazard  $f(t)/P(X>t)$"); ax.set_ylim(0,6)
ax.set_title("D. The empirical hazard turns; a Weibull cannot", fontsize=10, loc="left")
ax.legend(frameon=False, fontsize=8)

fig.tight_layout(); fig.savefig("weibull-figure.pdf")
json.dump(dict(a=a,b=b,cross=cross,am=am,bm=bm), open("data/drift.json","w"))
print("wrote weibull-figure.pdf")
