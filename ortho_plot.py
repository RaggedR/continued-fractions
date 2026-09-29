import numpy as np, json, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from numpy.polynomial import laguerre, hermite_e
from fractions import Fraction

z = np.load("data/ortho.npz"); g, D, b, m, s = z["g"], z["D"], float(z["b"]), float(z["m"]), float(z["s"])
rms = json.load(open("data/ortho_rms.json"))

def build(name, nm):
    if name == "lag":
        A = np.column_stack([np.exp(-b*g)*laguerre.lagval(b*g, np.eye(nm)[i]) for i in range(nm)])
    else:
        u = (g-m)/s
        A = np.column_stack([np.exp(-u*u/2)*hermite_e.hermeval(u, np.eye(nm)[i]) for i in range(nm)])
    c, *_ = np.linalg.lstsq(A, D, rcond=None); return A@c

fig, ax = plt.subplots(1, 3, figsize=(15.5, 4.6))

ax[0].plot(g, D, color="#123", lw=2.6, label="$D(t)$, the limiting shape")
ax[0].plot(g, build("lag",6), color="#c1443c", lw=1.6, ls="--", label="Laguerre, 6 terms")
ax[0].plot(g, build("her",6), color="#3f8f5f", lw=1.6, ls=":",  label="Hermite, 6 terms")
ax[0].axhline(0, color="#aaa", lw=.9); ax[0].set_xlim(0, 2.8)
ax[0].set_xlabel("$t=L(n)/\\sqrt{n}$"); ax[0].set_ylabel("$F_{\\rm emp}-F_{\\rm Weibull}$")
ax[0].set_title("A. The curve and two expansions", fontsize=11, loc="left")
ax[0].legend(frameon=False, fontsize=8.5)

ns = sorted(int(k) for k in rms)
for j,(lab,col,ls) in enumerate([("Laguerre","#c1443c","-"),("Hermite","#3f8f5f","-"),
                                 ("Legendre","#2f6f8f","--"),("Chebyshev","#c9a227",":")]):
    ax[1].semilogy(ns, [rms[str(i)][j] for i in ns], ls, color=col, lw=1.7, marker="o", ms=4, label=lab)
ax[1].axhline(np.sqrt((D**2).mean()), color="#999", lw=1, ls="-.", label="rms of $D$ itself")
ax[1].set_xlabel("terms"); ax[1].set_ylabel("rms residual")
ax[1].set_title("B. Weighted families win", fontsize=11, loc="left")
ax[1].legend(frameon=False, fontsize=8)

bs = np.linspace(4.56, 6.49, 200); rat = []
for bb in bs:
    A = np.column_stack([np.exp(-bb*g)*laguerre.lagval(bb*g, np.eye(6)[i]) for i in range(6)])
    c, *_ = np.linalg.lstsq(A, D, rcond=None); rat.append(c[1]/c[3])
rat = np.array(rat)
ax[2].plot(bs, rat, color="#123", lw=2)
seen = sorted({Fraction(float(x)).limit_denominator(12) for x in rat})
for f in seen:
    ax[2].axhline(float(f), color="#c1443c", lw=.6, alpha=.55)
ax[2].set_xlabel("Laguerre scale $b$  (all fits within 25% of best)")
ax[2].set_ylabel("$c_1/c_3$")
ax[2].set_title(f"C. The ratio sweeps {len(seen)} simple rationals", fontsize=11, loc="left")

fig.tight_layout(); fig.savefig("orthogonal.pdf")
print(f"wrote orthogonal.pdf   ({len(seen)} rationals crossed)")
