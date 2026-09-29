"""
Expand the limiting difference curve D(t) = F_empirical(t) - F_Weibull(t) in
several classical orthogonal families, and test whether the coefficients look
like integers or simple rationals.

D lives on [0, inf), vanishes at both ends and decays exponentially, so each
family is used with its own weight and an affine change of variable:

  Laguerre    D(t) = e^{-bt}      sum c_n L_n(bt)         natural on [0,inf)
  Hermite     D(t) = e^{-u^2/2}   sum c_n He_n(u),  u=(t-m)/s   (Gram-Charlier)
  Legendre    D(t) =              sum c_n P_n(2t/T - 1)    no weight, on [0,T]
  Chebyshev   D(t) =              sum c_n T_n(2t/T - 1)
"""
import numpy as np, math, json
from numpy.polynomial import laguerre, hermite_e, legendre, chebyshev
from scipy import stats
from scipy.optimize import minimize_scalar
from wfit import weibull_mle

T = 3.0
def curve(M):
    d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
    t = np.sort((L/np.sqrt(n))[n < M].astype(np.float64)); N = len(t)
    k, sc = weibull_mle(t)
    g = np.linspace(0, T, 1501)
    return g, np.searchsorted(t, g)/N - stats.weibull_min.cdf(g, k, 0, sc)

g, D = curve(1_000_000)
g6, D6 = curve(600_000)

def fit(basis, g, D, nmax, **kw):
    """least squares on the first nmax basis functions; returns coeffs, rms"""
    A = np.column_stack([basis(g, i, **kw) for i in range(nmax)])
    c, *_ = np.linalg.lstsq(A, D, rcond=None)
    return c, float(np.sqrt(((A@c - D)**2).mean()))

def lag(x, i, b): 
    e = np.zeros(i+1); e[i] = 1
    return np.exp(-b*x)*laguerre.lagval(b*x, e)
def her(x, i, m, s):
    u = (x-m)/s; e = np.zeros(i+1); e[i] = 1
    return np.exp(-u*u/2)*hermite_e.hermeval(u, e)
def leg(x, i):
    e = np.zeros(i+1); e[i] = 1
    return legendre.legval(2*x/T - 1, e)
def cheb(x, i):
    e = np.zeros(i+1); e[i] = 1
    return chebyshev.chebval(2*x/T - 1, e)

b = minimize_scalar(lambda b: fit(lag, g, D, 6, b=b)[1], bounds=(0.5, 12), method="bounded").x
ms = minimize_scalar(lambda m: fit(her, g, D, 6, m=m, s=0.45)[1], bounds=(0.05, 1.5), method="bounded").x
ss = minimize_scalar(lambda s: fit(her, g, D, 6, m=ms, s=s)[1], bounds=(0.1, 1.5), method="bounded").x
print(f"scale parameters chosen by least squares:  Laguerre b={b:.4f}   "
      f"Hermite m={ms:.4f} s={ss:.4f}\n")

print(f"{'terms':>6}{'Laguerre':>12}{'Hermite':>12}{'Legendre':>12}{'Chebyshev':>12}")
res = {}
for nm in range(2, 11):
    r = [fit(lag,g,D,nm,b=b)[1], fit(her,g,D,nm,m=ms,s=ss)[1],
         fit(leg,g,D,nm)[1], fit(cheb,g,D,nm)[1]]
    res[nm] = r
    print(f"{nm:>6}" + "".join(f"{x:>12.6f}" for x in r))
print(f"{'rms of D':>6}{np.sqrt((D**2).mean()):>12.6f}")

np.savez("data/ortho.npz", g=g, D=D, D6=D6, b=b, m=ms, s=ss)
json.dump({str(k_): v for k_, v in res.items()}, open("data/ortho_rms.json", "w"), indent=1)
