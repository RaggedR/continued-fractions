"""
Are the expansion coefficients integers, or simple rationals?

Coefficients carry the arbitrary overall scale of D, so only their RATIOS can
be meaningful.  Each ratio is tested by expanding it as a continued fraction
and seeing whether a short convergent already captures it -- and, decisively,
whether the ratio is STABLE between M = 600,000 and M = 10^6.  D itself still
drifts about 7% with M, so a ratio that moves more than its distance to a
candidate rational is noise wearing a suit.
"""
import numpy as np, math
from numpy.polynomial import laguerre, hermite_e
from fractions import Fraction

z = np.load("data/ortho.npz")
g, D, D6, b, m, s = z["g"], z["D"], z["D6"], float(z["b"]), float(z["m"]), float(z["s"])

def basis(name, x, i):
    e = np.zeros(i+1); e[i] = 1
    if name == "lag": return np.exp(-b*x)*laguerre.lagval(b*x, e)
    u = (x-m)/s;      return np.exp(-u*u/2)*hermite_e.hermeval(u, e)

def coef(name, y, nm):
    A = np.column_stack([basis(name, g, i) for i in range(nm)])
    return np.linalg.lstsq(A, y, rcond=None)[0]

for name, label in [("lag","LAGUERRE"), ("her","HERMITE")]:
    for nm in (4, 6):
        c  = coef(name, D,  nm)
        c6 = coef(name, D6, nm)
        big = np.argmax(np.abs(c))
        r, r6 = c/c[big], c6/c6[big]
        print(f"\n{label}, {nm} terms   (normalised by the largest, c[{big}])")
        print(f"{'n':>3}{'coeff':>12}{'ratio':>11}{'ratio at 6e5':>14}"
              f"{'drift':>9}{'nearest simple':>16}{'gap':>9}")
        for i in range(nm):
            f = Fraction(float(r[i])).limit_denominator(12)
            gap = abs(float(r[i]) - float(f))
            drift = abs(r[i]-r6[i])
            flag = "  <-" if (gap < 0.01 and drift < gap) else ""
            print(f"{i:>3}{c[i]:>12.5f}{r[i]:>11.4f}{r6[i]:>14.4f}"
                  f"{drift:>9.4f}{str(f):>16}{gap:>9.4f}{flag}")
print("\nA ratio is only worth a second look if its drift between the two M is")
print("SMALLER than its distance to the candidate rational.  Nothing marked means")
print("nothing survived that test.")
