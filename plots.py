"""
Redraw period-histogram.pdf: two pages, eight panels.

Page 1  the comb, why it is there, how it thins, and what removes it
Page 2  growth, spread, and the edge
"""
import math, numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages
from matplotlib.patches import Patch
from matplotlib.colors import LogNorm

d = np.load("data/periods.npz"); n, L = d["n"], d["L"]
N = int(d["N"]); t = L/np.sqrt(n)
EVEN, ODD, GREEN, GREY = "#2f6f8f", "#c1443c", "#3f8f5f", "#b9b3a8"

# smallest-prime-factor sieve, to ask whether n has a prime factor 3 mod 4
spf = np.zeros(N, dtype=np.int32)
for p in range(2, int(N**0.5)+1):
    if spf[p] == 0:
        spf[p*p::p][spf[p*p::p] == 0] = p
for i in range(2, N):
    if spf[i] == 0: spf[i] = i
def friendly(m):                      # no prime factor congruent to 3 mod 4
    while m > 1:
        p = spf[m]
        if p % 4 == 3: return False
        while m % p == 0: m //= p
    return True
fr = np.array([friendly(int(m)) for m in n])

odd = L % 2 == 1
ks = np.arange(1, 41)
cnt = np.array([(L == k).sum() for k in ks])

Ms = np.unique(np.round(np.logspace(3, 5, 60)).astype(int))
pct  = np.array([ (odd[n < M].mean()*100) for M in Ms ])
mean = np.array([ L[n < M].mean()          for M in Ms ])
edge = np.array([ t[n < M].max()           for M in Ms ])

with PdfPages("period-histogram.pdf") as pdf:
    # ---------------- page 1 ----------------
    fig = plt.figure(figsize=(11.7, 8.3))
    fig.suptitle(r"Period of the continued fraction of $\sqrt{n}$", fontsize=15, y=.975)
    fig.text(.5, .938, f"every non-square $n$ from 2 to {N-1} ({len(n):,} values)",
             ha="center", fontsize=10, color="#555")

    ax = fig.add_subplot(2,2,1)
    ax.bar(ks, cnt, color=[ODD if k%2 else EVEN for k in ks], width=.84)
    ax.set_title("1. The comb: even periods are common, odd periods are rare", fontsize=10)
    ax.set_xlabel("period length"); ax.set_ylabel("how many $n$")
    ax.legend(handles=[Patch(color=EVEN,label=f"even period  {(~odd).mean()*100:.1f}%"),
                       Patch(color=ODD ,label=f"odd period  {odd.mean()*100:.1f}%")],
              frameon=False, fontsize=8)

    ax = fig.add_subplot(2,2,2)
    sh = np.array([fr[L==k].mean() if (L==k).any() else 0 for k in ks])
    ax.bar(ks, sh*100, color=GREEN, width=.84)
    ax.bar(ks, (1-sh)*100, bottom=sh*100, color=GREY, width=.84)
    ax.set_title("2. Why: every odd-period column is entirely green", fontsize=10)
    ax.set_xlabel("period length"); ax.set_ylabel("share of the $n$ at that length")
    ax.set_yticks([0,25,50,75,100]); ax.set_yticklabels(["0","25%","50%","75%","100%"])
    ax.text(.5, -.30, f"numbers with an odd period AND a prime factor 3 mod 4: "
            f"{int((odd & ~fr).sum())}", transform=ax.transAxes, ha="center", fontsize=8.5)
    ax.legend(handles=[Patch(color=GREEN,label="every prime factor of $n$ is 2 or 1 mod 4"),
                       Patch(color=GREY ,label="$n$ has a prime factor 3 mod 4")],
              frameon=False, fontsize=8, loc="lower left", bbox_to_anchor=(0,1.06))

    ax = fig.add_subplot(2,2,3)
    ax.semilogx(Ms, pct, color=ODD, lw=1.8)
    ax.set_title("3. The odd column keeps thinning", fontsize=10)
    ax.set_xlabel("$M$"); ax.set_ylabel("% of $n<M$ with odd period")
    ax.set_ylim(0, 20)
    for M in (1000, 10000, 100000):
        v = odd[n < M].mean()*100
        ax.plot([M],[v], "o", ms=4, color=ODD)
        ax.annotate(f"{v:.2f}%", (M,v), textcoords="offset points",
                    xytext=(-4,7), fontsize=8, ha="right")

    ax = fig.add_subplot(2,2,4)
    ax.hist(t, bins=np.linspace(0, 2.6, 53), color=EVEN)
    ax.set_title(r"4. Divided by $\sqrt{n}$, the comb vanishes", fontsize=10)
    ax.set_xlabel(r"$L(n)/\sqrt{n}$"); ax.set_ylabel("how many $n$")
    ax.text(.97,.93, f"max {t.max():.2f}", transform=ax.transAxes, ha="right", fontsize=9)

    fig.tight_layout(rect=[0,0,1,.93]); pdf.savefig(fig); plt.close(fig)

    # ---------------- page 2 ----------------
    fig = plt.figure(figsize=(11.7, 8.3))
    fig.suptitle("Growth, spread, and the edge", fontsize=15, y=.975)

    ax = fig.add_subplot(2,1,1)
    hb = ax.hexbin(n, L, gridsize=(150,60), bins="log", cmap="viridis", mincnt=1)
    xs = np.linspace(1, N, 400)
    ax.plot(xs, t.max()*np.sqrt(xs), color=ODD, lw=1.4,
            label=rf"${t.max():.2f}\sqrt{{n}}$, the observed edge")
    ax.plot(xs, (L/np.sqrt(n)).mean()*np.sqrt(xs), color="w", lw=1.4, ls="--",
            label=rf"${t.mean():.2f}\sqrt{{n}}$, near the mean")
    ax.set_title("5. Every period, plotted against $n$ (shading is how many, on a log scale)", fontsize=10)
    ax.set_xlabel("$n$"); ax.set_ylabel("period length $L(n)$"); ax.set_ylim(0, L.max()*1.02)
    ax.legend(frameon=False, fontsize=8.5, loc="upper left")
    fig.colorbar(hb, ax=ax, pad=.01)

    ax = fig.add_subplot(2,3,4)
    ax.loglog(Ms, mean, color=EVEN, lw=1.8, label="mean $L$")
    sl = np.polyfit(np.log(Ms), np.log(mean), 1)[0]
    ax.loglog(Ms, mean[0]*(Ms/Ms[0])**sl, color=ODD, lw=1, ls="--", label=f"slope {sl:.3f}")
    ax.loglog(Ms, mean[0]*(Ms/Ms[0])**.5,  color="#888", lw=1, ls=":",  label="slope 0.5")
    ax.set_title(r"6. The mean grows slower than $\sqrt{M}$", fontsize=10)
    ax.set_xlabel("$M$"); ax.set_ylabel("mean period, $n<M$"); ax.legend(frameon=False, fontsize=8)

    ax = fig.add_subplot(2,3,5)
    ax.semilogx(Ms, edge, color=ODD, lw=1.8)
    ax.set_title("7. The right edge is not hard, it drifts", fontsize=10)
    ax.set_xlabel("$M$"); ax.set_ylabel(r"largest $L(n)/\sqrt{n}$ for $n<M$")

    ax = fig.add_subplot(2,3,6)
    ax.hist(L, bins=np.linspace(0, L.max(), 76), color=EVEN)
    ax.set_title("8. The full distribution, all period lengths", fontsize=10)
    ax.set_xlabel("period length"); ax.set_ylabel("how many $n$")
    ax.text(.97,.93, f"mean {L.mean():.1f}  median {int(np.median(L))}  longest {L.max()}",
            transform=ax.transAxes, ha="right", fontsize=8.5)

    fig.tight_layout(rect=[0,0,1,.94]); pdf.savefig(fig); plt.close(fig)

print(f"period-histogram.pdf: 2 pages, 8 panels")
print(f"  odd {odd.mean()*100:.2f}%   max L/sqrt(n) {t.max():.4f}   loglog slope {sl:.4f}")
print(f"  odd period AND a prime factor 3 mod 4: {int((odd & ~fr).sum())}")
