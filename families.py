"""
Which basis actually fits D(t) better, and why.

Key point to test: orthogonal polynomials of degree < n span exactly the same
space as {1, x, ..., x^(n-1)}.  So an UNWEIGHTED expansion in Legendre,
Chebyshev or plain monomials must give the identical least-squares fit; only
conditioning differs.  Any real gain comes from the WEIGHT, not the polynomials.
"""
import numpy as np, math
from numpy.polynomial import laguerre, hermite_e, legendre, chebyshev
from scipy import stats
from scipy.special import eval_genlaguerre
from scipy.optimize import minimize_scalar
from wfit import weibull_mle

d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
t = np.sort((L/np.sqrt(n)).astype(np.float64)); N = len(t)
K, S = weibull_mle(t)
T = 3.0; g = np.linspace(0, T, 1501)
D = np.searchsorted(t, g)/N - stats.weibull_min.cdf(g, K, 0, S)
z = np.load("data/ortho.npz"); b, m, s = float(z["b"]), float(z["m"]), float(z["s"])

u_pit = stats.weibull_min.cdf(g, K, 0, S)          # probability integral transform

def rms(A):
    c, *_ = np.linalg.lstsq(A, D, rcond=None)
    return float(np.sqrt(((A@c - D)**2).mean()))

def cols(f, nm): return np.column_stack([f(i) for i in range(nm)])

FAM = {
 "monomials  1,x,x^2,...":   lambda nm: cols(lambda i: g**i, nm),
 "Legendre (no weight)":     lambda nm: cols(lambda i: legendre.legval(2*g/T-1, np.eye(nm)[i]), nm),
 "Chebyshev (no weight)":    lambda nm: cols(lambda i: chebyshev.chebval(2*g/T-1, np.eye(nm)[i]), nm),
 "Hermite x Gaussian":       lambda nm: cols(lambda i: np.exp(-((g-m)/s)**2/2)*hermite_e.hermeval((g-m)/s, np.eye(nm)[i]), nm),
 "Laguerre x exp":           lambda nm: cols(lambda i: np.exp(-b*g)*laguerre.lagval(b*g, np.eye(nm)[i]), nm),
 "gen. Laguerre a=1, x t":   lambda nm: cols(lambda i: b*g*np.exp(-b*g)*eval_genlaguerre(i,1,b*g), nm),
 "sine series after PIT":    lambda nm: cols(lambda i: np.sin((i+1)*math.pi*u_pit), nm),
 "shifted Legendre after PIT":lambda nm: cols(lambda i: u_pit*(1-u_pit)*legendre.legval(2*u_pit-1, np.eye(nm)[i]), nm),
}

print(f"{'family':<28}" + "".join(f"{k:>10}" for k in ("4 terms","6","8","10")))
for name, mk in FAM.items():
    print(f"{name:<28}" + "".join(f"{rms(mk(nm)):>10.6f}" for nm in (4,6,8,10)))
print(f"{'rms of D itself':<28}{np.sqrt((D**2).mean()):>10.6f}")

# ---- further families worth trying -------------------------------------
from scipy.special import eval_chebyt, binom
from scipy.optimize import minimize_scalar as ms1

def gl_alpha(al, nm):
    return cols(lambda i: (b*g)**al*np.exp(-b*g)*eval_genlaguerre(i, al, b*g), nm)
al = ms1(lambda a: rms(gl_alpha(a, 6)), bounds=(0.05, 4), method="bounded").x

def ratcheb(beta, nm):           # rational Chebyshev on the half line
    x = (g-beta)/(g+beta)
    return cols(lambda i: (1-x)/2*eval_chebyt(i, x), nm)
be = ms1(lambda B: rms(ratcheb(B, 6)), bounds=(0.05, 3), method="bounded").x

def bern(nm):                    # Bernstein after the probability transform
    return cols(lambda i: binom(nm-1, i)*u_pit**i*(1-u_pit)**(nm-1-i), nm)

def weib_basis(nm):              # CDFs of Weibulls on a geometric ladder of scales
    return cols(lambda i: stats.weibull_min.cdf(g, 1.0, 0, S*2.0**(i-nm//2)), nm)

EXTRA = {
 f"gen. Laguerre, fitted a={al:.2f}": lambda nm: gl_alpha(al, nm),
 f"rational Chebyshev, b={be:.2f}":   lambda nm: ratcheb(be, nm),
 "Bernstein after PIT":               bern,
 "mixture of exponential CDFs":       weib_basis,
}
print()
for name, mk in EXTRA.items():
    print(f"{name:<28}" + "".join(f"{rms(mk(nm)):>10.6f}" for nm in (4,6,8,10)))
