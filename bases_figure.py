"""Convergence of every basis tried, against the accuracy of D itself."""
import numpy as np, math, json, matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from numpy.polynomial import laguerre, hermite_e, legendre
from scipy import stats
from scipy.special import eval_genlaguerre, eval_chebyt, binom
from scipy.optimize import minimize_scalar
from wfit import weibull_mle

d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
t = np.sort((L/np.sqrt(n)).astype(np.float64)); N = len(t)
K, S = weibull_mle(t); T = 3.0
g = np.linspace(0, T, 1501)
D = np.searchsorted(t, g)/N - stats.weibull_min.cdf(g, K, 0, S)
z = np.load("data/ortho.npz"); b, m, s = float(z["b"]), float(z["m"]), float(z["s"])
floor = float(np.sqrt(((z["D"]-z["D6"])**2).mean()))
u = stats.weibull_min.cdf(g, K, 0, S)

def rms(A):
    c, *_ = np.linalg.lstsq(A, D, rcond=None)
    return float(np.sqrt(((A@c - D)**2).mean()))
def cols(f, nm): return np.column_stack([f(i) for i in range(nm)])

al = minimize_scalar(lambda a: rms(cols(lambda i:(b*g)**a*np.exp(-b*g)*eval_genlaguerre(i,a,b*g),6)),
                     bounds=(.05,4), method="bounded").x
be = minimize_scalar(lambda B: rms(cols(lambda i:(1-(g-B)/(g+B))/2*eval_chebyt(i,(g-B)/(g+B)),6)),
                     bounds=(.05,3), method="bounded").x

FAM = [
 ("monomials = Legendre = Chebyshev", "#999","-",  lambda nm: cols(lambda i: g**i, nm)),
 ("Hermite $\\times$ Gaussian",       "#3f8f5f","-",lambda nm: cols(lambda i: np.exp(-((g-m)/s)**2/2)*hermite_e.hermeval((g-m)/s,np.eye(nm)[i]), nm)),
 ("Laguerre $\\times$ $e^{-bt}$",     "#c1443c","-",lambda nm: cols(lambda i: np.exp(-b*g)*laguerre.lagval(b*g,np.eye(nm)[i]), nm)),
 (f"gen. Laguerre, $\\alpha={al:.2f}$","#8a4f9f","--",lambda nm: cols(lambda i:(b*g)**al*np.exp(-b*g)*eval_genlaguerre(i,al,b*g), nm)),
 (f"rational Chebyshev, $\\beta={be:.2f}$","#2f6f8f","--",lambda nm: cols(lambda i:(1-(g-be)/(g+be))/2*eval_chebyt(i,(g-be)/(g+be)), nm)),
 ("exponential CDFs",                 "#c9a227","-.",lambda nm: cols(lambda i: stats.weibull_min.cdf(g,1.,0,S*2.**(i-nm//2)), nm)),
 ("Bernstein after PIT",              "#777","--", lambda nm: cols(lambda i: binom(nm-1,i)*u**i*(1-u)**(nm-1-i), nm)),
 ("sine series after PIT",            "#444",":",  lambda nm: cols(lambda i: np.sin((i+1)*math.pi*u), nm)),
]
ns = list(range(2,11)); out={}
fig, ax = plt.subplots(figsize=(9.5,5.8))
for lab,c,ls,mk in FAM:
    v=[rms(mk(nm)) for nm in ns]; out[lab]=v
    ax.semilogy(ns,v,ls,color=c,lw=1.8,marker="o",ms=4,label=lab)
ax.axhspan(0,floor,color="#c1443c",alpha=.10,lw=0)
ax.axhline(floor,color="#c1443c",lw=1.1,ls="--")
ax.text(9.9,floor*.72,f"$D$ is only known to {floor:.6f}",ha="right",fontsize=8.5,color="#c1443c")
ax.axhline(np.sqrt((D**2).mean()),color="#999",lw=1,ls="-.")
ax.text(2.1,np.sqrt((D**2).mean())*1.08,"rms of $D$ itself",fontsize=8.5,color="#777")
ax.set_xlabel("number of terms"); ax.set_ylabel("rms residual")
ax.set_title("Every basis tried, against the accuracy of the curve itself", fontsize=12)
ax.legend(frameon=False, fontsize=8.5, loc="lower left")
fig.tight_layout(); fig.savefig("bases-figure.pdf")
json.dump({"floor":floor,"alpha":al,"beta":be,"ns":ns,"rms":out}, open("data/bases.json","w"), indent=1)
print(f"floor {floor:.6f}   alpha {al:.3f}   beta {be:.3f}")
