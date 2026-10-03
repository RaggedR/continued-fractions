"""
The 2x2 matrix picture of the period of sqrt(n).

Everything in matrices.tex is generated or checked here.

    M(a) = [[a,1],[1,0]] = T^a . J,   T = [[1,1],[0,1]],  J = [[0,1],[1,0]]

so a continued fraction is a word in translations, and the period of sqrt(n) is
a hyperbolic conjugacy class in GL_2(Z).  Checks:

  (1)  A = M(a_1)...M(a_L)  has  tr A = 2x  and  det A = (-1)^L,
       where (x,y) is the fundamental solution of x^2 - n y^2 = (-1)^L.
  (2)  the trace IS the geodesic length, with the period's parity deciding
       which hyperbolic function:  det A = +1 (L even) gives tr A = 2 cosh R,
       det A = -1 (L odd) gives tr A = 2 sinh R.
  (3)  A^T is the matrix of the reversed period (M(a) is symmetric), which is
       the palindrome of palindrome.tex read as a statement about conjugacy.
  (4)  Trichotomy by disc = tr^2 - 4 det: hyperbolic / parabolic / elliptic,
       and the elliptic fixed points lie in Q(i) and Q(omega) only.
  (5)  The stabiliser of a rational is parabolic, conjugate to <T>.
  (6)  Why L/R falls ~10% short of the Levy constant 12 log 2 / pi^2: the
       forced 2a_0 term.  Removing it recovers the prediction.
"""
import math, random
import numpy as np

I2 = np.array([[1, 0], [0, 1]], dtype=object)
T  = np.array([[1, 1], [0, 1]], dtype=object)
J  = np.array([[0, 1], [1, 0]], dtype=object)

def M(a):
    return np.array([[a, 1], [1, 0]], dtype=object)

def word(qs):
    A = I2.copy()
    for a in qs:
        A = A @ M(a)
    return A

def tr(A):  return int(A[0, 0] + A[1, 1])
def det(A): return int(A[0, 0] * A[1, 1] - A[0, 1] * A[1, 0])
def disc(A): return tr(A)**2 - 4 * det(A)

def kind(A):
    d = disc(A)
    return "hyperbolic" if d > 0 else ("parabolic" if d == 0 else "elliptic")

def cf_sqrt(n):
    """PQa: a_0 and the period, plus log of each complete quotient (sums to R)."""
    a0 = math.isqrt(n)
    if a0 * a0 == n:
        return a0, [], []
    P, Q, a = 0, 1, a0
    per, logs = [], []
    while True:
        P = a * Q - P
        Q = (n - P * P) // Q
        a = (a0 + P) // Q
        per.append(a)
        logs.append(math.log((P + math.sqrt(n)) / Q))
        if Q == 1 and P == a0:
            break
    return a0, per, logs

def order(A, cap=13):
    X = A.copy()
    for k in range(1, cap):
        if (X == I2).all():
            return k
        X = X @ A
    return None


def check_alphabet():
    print("(0)  M(a) = T^a . J")
    for a in (1, 2, 5, 12):
        Ta = np.array([[1, a], [0, 1]], dtype=object)
        assert ((Ta @ J) == M(a)).all()
        print(f"       a={a:>3}:  T^a J = {(Ta @ J).tolist()}   ok")

def check_trace():
    print("\n(1,2,3)  trace, determinant, transpose")
    print(f"{'n':>7} {'L':>4} {'det':>4} {'tr A':>22} {'2x':>22} {'norm':>5}"
          f" {'2cosh R / 2sinh R':>19} {'A^T=rev':>8}")
    for n in (2, 3, 7, 13, 46, 61, 109, 151, 211, 421, 1621):
        a0, per, logs = cf_sqrt(n)
        L, A = len(per), word(per)
        B = word([a0] + per[:-1])                     # convergent p_{L-1}/q_{L-1}
        x, y = int(B[0, 0]), int(B[1, 0])
        R = sum(logs)
        rev = ((A.T) == word(per[::-1])).all()
        h = 2*math.cosh(R) if L % 2 == 0 else 2*math.sinh(R)
        print(f"{n:>7} {L:>4} {det(A):>4} {tr(A):>22} {2*x:>22} {x*x-n*y*y:>5}"
              f" {h:>19.7g} {str(rev):>8}")
        assert tr(A) == 2 * x
        assert det(A) == (-1)**L
        assert x * x - n * y * y == (-1)**L
        assert rev
        assert abs(h / abs(tr(A)) - 1) < 1e-9

def check_trichotomy():
    print("\n(4)  the trichotomy, and the torsion of SL_2(Z)")
    named = [("I",        [[1, 0], [0, 1]]),
             ("-I",       [[-1, 0], [0, -1]]),
             ("T",        [[1, 1], [0, 1]]),
             ("S",        [[0, -1], [1, 0]]),
             ("ST",       [[0, -1], [1, 1]]),
             ("(ST)^2",   [[-1, -1], [1, 0]]),
             ("M(1)",     [[1, 1], [1, 0]]),
             ("M(2)M(2)", [[5, 2], [2, 1]])]
    print(f"{'A':>9} {'tr':>4} {'det':>4} {'disc':>6} {'kind':>11} {'order':>6}  fixed points in")
    for nm, Am in named:
        A = np.array(Am, dtype=object)
        a, b, c = int(A[1, 0]), tr(A) - 2 * int(A[0, 0]), -int(A[0, 1])
        fd = b * b - 4 * a * c if a else None
        fld = "Q" if fd == 0 else (f"Q(sqrt({fd}))" if fd is not None else "infinity only")
        print(f"{nm:>9} {tr(A):>4} {det(A):>4} {disc(A):>6} {kind(A):>11} {str(order(A)):>6}  {fld}")

def check_parabolic_stabiliser():
    print("\n(5)  stabiliser of a rational is conjugate to <T>, hence parabolic")
    def egcd(a, b):
        if b == 0: return a, 1, 0
        d, u, v = egcd(b, a % b); return d, v, u - (a // b) * v
    for p, q in [(0, 1), (3, 1), (2, 5), (-7, 11)]:
        _, u, v = egcd(p, q)
        G = np.array([[p, -v], [q, u]], dtype=object)
        assert det(G) == 1
        Gi = np.array([[G[1, 1], -G[0, 1]], [-G[1, 0], G[0, 0]]], dtype=object)
        A = G @ T @ Gi
        num, den = int(A[0, 0] * p + A[0, 1] * q), int(A[1, 0] * p + A[1, 1] * q)
        assert num * q == den * p
        print(f"       p/q = {p}/{q}:  G T G^-1 = {A.tolist()}   tr={tr(A)}  disc={disc(A)}  fixes p/q")

def check_levy(seed=1):
    print("\n(6)  L/R against the Levy constant, with and without the forced 2a_0")
    lam = math.pi**2 / (12 * math.log(2))
    print(f"       lambda = {lam:.6f},   1/lambda = {1/lam:.6f}")
    print(f"{'band':>20} {'#':>6} {'R/L':>9} {'R/L less 2a_0':>15} {'excess':>9} {'log(2a0)/L':>11}")
    rng = random.Random(seed)
    for lo, hi in [(2, 10**3), (10**3, 10**4), (10**4, 10**5), (10**5, 10**6)]:
        ns = [n for n in range(lo, hi) if math.isqrt(n)**2 != n]
        if len(ns) > 4000:
            ns = rng.sample(ns, 4000)
        full, trim, pred = [], [], []
        for n in ns:
            a0, per, logs = cf_sqrt(n)
            L, R = len(per), sum(logs)
            full.append(R / L)
            if L > 1:
                trim.append((R - logs[-1]) / (L - 1))
                pred.append(logs[-1] / L)
        f, t, p = np.mean(full), np.mean(trim), np.mean(pred)
        print(f"[{lo:>7},{hi:>8}) {len(ns):>6} {f:>9.5f} {t:>15.5f} {f-lam:>9.5f} {p:>11.5f}")

if __name__ == "__main__":
    check_alphabet()
    check_trace()
    check_trichotomy()
    check_parabolic_stabiliser()
    check_levy()
    print("\nall assertions passed")
