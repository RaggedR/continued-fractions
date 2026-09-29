"""Redraw the comb histogram and the L(n)/sqrt(n) density."""
import math, numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

d = np.load("data/periods.npz"); n, L = d["n"], d["L"]
t = L/np.sqrt(n)

fig, ax = plt.subplots(figsize=(9,4.2))
ks = np.arange(1,41)
cnt = np.array([(L==k).sum() for k in ks])
cols = ["#c44"if k%2 else "#368" for k in ks]
ax.bar(ks, cnt, color=cols, width=0.82)
ax.set_xlabel("period length $L(n)$"); ax.set_ylabel("count")
ax.set_title(f"Period of $\\sqrt{{n}}$, $n<10^5$  —  {(L>40).sum():,} of {len(L):,} have $L>40$")
ax.set_xticks([1,5,10,15,20,25,30,35,40])
from matplotlib.patches import Patch
ax.legend(handles=[Patch(color="#368",label="even $L$  (88.5%)"),
                   Patch(color="#c44",label="odd $L$  (11.5%)")], frameon=False)
fig.tight_layout(); fig.savefig("period-histogram.pdf")

fig, axes = plt.subplots(1,2, figsize=(11,4.2))
axes[0].hist(t, bins=np.linspace(0,2.6,41), color="#368", edgecolor="white", linewidth=.4)
axes[0].set_xlabel("$t=L(n)/\\sqrt{n}$"); axes[0].set_ylabel("count")
axes[0].set_title("the comb is gone")
for lo,hi,c in [(10000,40000,"#368"),(60000,100000,"#c44")]:
    m=(n>=lo)&(n<hi)
    h,e = np.histogram(t[m], bins=np.linspace(0,2.6,41), density=True)
    axes[1].semilogy((e[:-1]+e[1:])/2, h, color=c, lw=1.6,
                     label=f"$n\\in[{lo//1000}\\mathrm{{k}},{hi//1000}\\mathrm{{k}})$")
axes[1].set_xlabel("$t$"); axes[1].set_ylabel("density (log)")
axes[1].set_title("two bands do not coincide: the law drifts")
axes[1].legend(frameon=False)
fig.tight_layout(); fig.savefig("distribution.pdf")
print("wrote period-histogram.pdf, distribution.pdf")
print(f"  bars 1..40 total {cnt.sum():,};  L>40: {(L>40).sum():,}")
