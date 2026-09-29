"""
Is "integer coefficients" a well-posed question here?

The Laguerre expansion carries a free scale b, chosen by least squares.  If the
fit quality is flat in b over a range, then the coefficients -- and every ratio
between them -- can be tuned continuously, and hitting a rational is a choice
rather than a discovery.
"""
import numpy as np
from numpy.polynomial import laguerre
from fractions import Fraction

z = np.load("data/ortho.npz"); g, D = z["g"], z["D"]
def coefs(b, nm=6):
    A = np.column_stack([np.exp(-b*g)*laguerre.lagval(b*g, np.eye(nm)[i]) for i in range(nm)])
    c, *_ = np.linalg.lstsq(A, D, rcond=None)
    return c, float(np.sqrt(((A@c - D)**2).mean()))

print(f"{'b':>7}{'rms':>11}{'c1/c3':>10}{'c4/c3':>10}{'c5/c3':>10}   nearest simple (c1/c3)")
for b in [4.4, 4.8, 5.2, 5.657, 6.0, 6.5, 7.0]:
    c, r = coefs(b)
    q = c/c[3]
    f = Fraction(float(q[1])).limit_denominator(12)
    print(f"{b:>7.3f}{r:>11.6f}{q[1]:>10.4f}{q[4]:>10.4f}{q[5]:>10.4f}   {str(f):>8}"
          f"  (gap {abs(float(q[1])-float(f)):.4f})")

cs, rs = coefs(5.657)
best = rs
print(f"\nrange of b whose rms is within 25% of the best ({best:.6f}):")
bs = np.linspace(3.5, 9, 400)
ok = [b for b in bs if coefs(b)[1] < 1.25*best]
print(f"   b from {min(ok):.2f} to {max(ok):.2f}")
q1 = [coefs(b)[0][1]/coefs(b)[0][3] for b in (min(ok), max(ok))]
print(f"   over that range c1/c3 sweeps {q1[0]:.3f} to {q1[1]:.3f}")
print(f"   number of rationals with denominator <= 12 inside that sweep: "
      f"{len({Fraction(x).limit_denominator(12) for x in np.linspace(min(q1),max(q1),400)})}")
