"""
Continued fractions over the Eisenstein integers Z[w], w = exp(2 pi i/3).

Hurwitz's algorithm, transplanted from Z[i] to the hexagonal lattice: round to
the NEAREST Eisenstein integer, subtract, invert, repeat.

    z_{k+1} = 1 / (z_k - round(z_k)),     round: C -> Z[w]
"""
from mpmath import mp, mpf, mpc, sqrt, cbrt, floor, fabs
mp.dps = 120
W = mpc(-0.5, 0) + mpc(0, 1)*sqrt(3)/2          # w = -1/2 + i sqrt3/2

def eis_round(z):
    """nearest point of Z[w]; z = a + b w  =>  b = 2 Im z / sqrt3, a = Re z + b/2"""
    b = 2*z.imag/sqrt(3); a = z.real + b/2
    best, bd = None, None
    for da in (-1,0,1):
        for db in (-1,0,1):
            A, B = int(floor(a))+da, int(floor(b))+db
            d = fabs(z - (A + B*W))
            if bd is None or d < bd: best, bd = (A,B), d
    return best

def ecf(z, terms=40):
    out = []
    for _ in range(terms):
        A,B = eis_round(z); out.append((A,B))
        d = z - (A + B*W)
        if fabs(d) < mpf(10)**-100: break
        z = 1/d
    return out

def find_period(seq, lo=3, maxp=12):
    """smallest p such that the tail repeats with period p"""
    for p in range(1, maxp+1):
        if len(seq) < lo+3*p: continue
        if all(seq[i]==seq[i+p] for i in range(lo, len(seq)-p)):
            return p
    return None

tests = [
    ("sqrt(2)          quadratic over Q",      sqrt(mpf(2))),
    ("(1+sqrt5)/2      quadratic over Q",      (1+sqrt(mpf(5)))/2),
    ("sqrt(-7)         quadratic over Q",      mpc(0,1)*sqrt(mpf(7))),
    ("sqrt(2)*w        quadratic over Q(w)",   sqrt(mpf(2))*W),
    ("cbrt(2)          CUBIC over Q(w)",       cbrt(mpf(2))),
    ("cbrt(2)*w        CUBIC over Q(w)",       cbrt(mpf(2))*W),
    ("cbrt(5)          CUBIC over Q(w)",       cbrt(mpf(5))),
]
for name, z in tests:
    s = ecf(z, 40)
    p = find_period(s[:28])
    print(f"{name:<34} period {str(p):>4}   first terms {s[:8]}")
