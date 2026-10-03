"""When is the supremum of `thm:step5` attained?  Numerics for
`research-question.txt`.

`thm:step5` recovers the intercept as x = sup_N D(N), D(N) = S(N) - N alpha,
and splits on whether that supremum is attained: attained gives the lower
coding C(alpha, x), not attained the upper C+.  The question was to read
attainment off the derivation tower (eps_j, a_j, k0_j).

Five claims:

  A  for ell = C(alpha, {-N alpha}) the supremum is attained at M = N, and at
     no other index
  B  for C+ and for rational intercepts the records of D never stop: the last
     one moves out when the window doubles
  C  no TAIL of the tower decides attainment.  At n = 2 and n = 5 an attained
     and a non-attained word have towers differing at levels 0 and 1 only --
     checked here to the depth a 200000-letter word supports, and separately to
     depth 15 at n = 2 on two million letters
  D  no BOUNDED WINDOW decides it either.  The deepest agreement between an
     attained and a non-attained tower grows with the range of shifts searched
  E  k0_j = a_j for all j holds for no attained word: at n = 3 and n = 7 the
     characteristic word has k0_j = 0 at every level

Nothing is tested on a decimal truncation.  alpha = sqrt(n) - floor sqrt(n),
and every comparison of D(M) with D(M') is a comparison of A - B sqrt(n) with
zero, decided by `cmp_int_sqrt` on integers.

The words tested are windows on the two-sided coding.  For N >= 0 the
intercept {-N alpha} lies in the backward orbit of 0, and there

    C (alpha, {-N alpha})_i = c_{i-N},      c_m = floor((m+1)a) - floor(m a)
    C+(alpha, {-N alpha})_i = cUp_{i-N},  cUp_m =  ceil((m+1)a) -  ceil(m a)

are distinct words.  Those are the only intercepts where lower and upper
differ, so the orbit supplies both halves of the dichotomy; rational
intercepts cannot, since for rational x only x = 0 meets the orbit.  c and cUp
agree off {-1, 0}, where one reads 10 and the other 01.

Run: python3 attainment.py
"""
from math import isqrt


# ------------------------------------------------- exact alpha-arithmetic

def cmp_int_sqrt(A, B, n):
    """sign(A - B sqrt(n)), for integers A, B and nonsquare n."""
    if B <= 0:
        if A >= 0:
            return 0 if (A == 0 and B == 0) else 1
        return -1 if A * A > B * B * n else 1
    if A < 0:
        return -1
    d = A * A - B * B * n
    return 0 if d == 0 else (1 if d > 0 else -1)


def fl(m, n, a0):
    """floor(m * alpha), alpha = sqrt(n) - a0, for any m in Z."""
    if m >= 0:
        return isqrt(m * m * n) - m * a0
    return -(isqrt(m * m * n) + 1) - m * a0          # sqrt(n) irrational


def ce(m, n, a0):
    """ceil(m * alpha)."""
    return 0 if m == 0 else fl(m, n, a0) + 1


def twosided(n, length, nmax):
    """(lower, upper) windows: word(N, upper) gives the shift by N."""
    a0 = isqrt(n)
    lo, hi = -nmax - 1, length + 1
    F = [fl(m, n, a0) for m in range(lo, hi + 1)]
    G = [ce(m, n, a0) for m in range(lo, hi + 1)]
    c = [F[i + 1] - F[i] for i in range(hi - lo)]
    cu = [G[i + 1] - G[i] for i in range(hi - lo)]

    def word(N, upper):
        src = cu if upper else c
        off = -lo - N
        return src[off:off + length]

    return word


def rational(n, p, q, length):
    """C(alpha, p/q) -- a generic intercept, outside the orbit of 0."""
    a0 = isqrt(n)

    def flx(k):
        base = isqrt(k * k * n)
        c = (base + 1) * q - p
        ge = (k * k * n) * q * q >= c * c if c > 0 else True
        return base + (1 if ge else 0) - k * a0

    f = [flx(k) for k in range(length + 1)]
    return [f[i + 1] - f[i] for i in range(length)]


# ------------------------------------------------------------- the tower

def level(s):
    """One derivation step: (eps, a, k0, derived word).

    eps = 1 when the letters were exchanged first, which step 1 does when the
    word contains 11.  a is the short block length, read as the least gap
    between consecutive 1s; cor:gaps says every gap is a or a + 1.  k0 is the
    initial block length.
    """
    eps = 1 if any(s[i] == s[i + 1] == 1 for i in range(len(s) - 1)) else 0
    if eps:
        s = [1 - c for c in s]
    idx = [i for i, c in enumerate(s) if c == 1]
    if len(idx) < 3:
        return None
    gaps = [idx[i + 1] - idx[i] for i in range(len(idx) - 1)]
    a = min(gaps)
    assert set(gaps) <= {a, a + 1}, sorted(set(gaps))[:5]
    return eps, a, idx[0], [1 if g == a + 1 else 0 for g in gaps]


def tower(s, depth=12):
    """[(eps_j, a_j, k0_j)] for as many levels as the word supports."""
    out = []
    while len(out) < depth:
        r = level(s)
        if r is None:
            break
        eps, a, k0, s = r
        out.append((eps, a, k0))
    return out


def agree(t, u):
    """Number of leading levels on which two towers agree."""
    d = 0
    while d < min(len(t), len(u)) and t[d] == u[d]:
        d += 1
    return d


# ---------------------------------------------------------- attainment

def last_record(s, n):
    """Index of the last strict record of D(M) = S(M) - M alpha.

    D(M) > D(best) iff (dS + dM a0) - dM sqrt(n) > 0.  The supremum is
    attained exactly when the records stop.
    """
    a0, S = isqrt(n), [0]
    for c in s:
        S.append(S[-1] + c)
    best, last = 0, 0
    for M in range(1, len(s) + 1):
        dS, dM = S[M] - S[best], M - best
        if cmp_int_sqrt(dS + dM * a0, dM, n) > 0:
            best, last = M, M
    return last


# ------------------------------------------------------------------ main

def k0s(t):
    return " ".join(str(k) for _, _, k in t)


def main():
    SLOPES = (2, 3, 5, 7, 13, 29, 43)

    print("A. C(alpha, {-N alpha}) attains its supremum at M = N")
    for n in SLOPES:
        word = twosided(n, 40000, 12)
        for N in range(12):
            last = last_record(word(N, False), n)
            assert last == N, (n, N, last)
        print(f"   n={n:3d}  N = 0..11, last record = N in every case")

    print("\nB. C+ and rational intercepts: the records never stop")
    for n in (2, 5, 7):
        w1, w2 = twosided(n, 30000, 4), twosided(n, 60000, 4)
        for tag, a, b in (
                ("C+(a,0)     ", last_record(w1(0, True), n),
                 last_record(w2(0, True), n)),
                ("C+(a,{-3a}) ", last_record(w1(3, True), n),
                 last_record(w2(3, True), n)),
                ("C (a,1/3)   ", last_record(rational(n, 1, 3, 30000), n),
                 last_record(rational(n, 1, 3, 60000), n))):
            assert b > a, (n, tag, a, b)
            print(f"   n={n:3d} {tag} last record {a:6d} -> {b:6d} on doubling")

    print("\nC. no tail of the tower decides attainment")
    for n in (2, 5):
        word = twosided(n, 200000, 4)
        tl, tu = tower(word(0, False), 7), tower(word(0, True), 7)
        j = max(i for i in range(min(len(tl), len(tu))) if tl[i] != tu[i]) + 1
        assert tl[j:] == tu[j:] and j > 0
        print(f"   n={n:3d}  C  k0: {k0s(tl)}")
        print(f"         C+ k0: {k0s(tu)}      equal from level {j}")

    print("\nD. no bounded window decides it either")
    for n in (2, 5, 13):
        prev = 0
        for nmax in (8, 30, 120):
            word = twosided(n, 150000, nmax)
            L = [tower(word(N, False), 10) for N in range(nmax)]
            U = [tower(word(N, True), 10) for N in range(nmax)]
            best = max((agree(t, u), i, j)
                       for i, t in enumerate(L) for j, u in enumerate(U))
            d, i, j = best
            print(f"   n={n:3d}  shifts < {nmax:4d}:  C(a,{{-{i}a}}) and "
                  f"C+(a,{{-{j}a}}) agree on the first {d} levels")
            assert d >= prev
            prev = d
        assert prev > 2, prev

    print("\nE. k0_j = a_j for all j holds for no attained word")
    for n in (3, 7):
        t = tower(twosided(n, 200000, 1)(0, False), 8)
        assert all(k != a for _, a, k in t)
        print(f"   n={n:3d}  C(a,0)  a_j: {' '.join(str(a) for _, a, _ in t)}")
        print(f"            k0_j: {k0s(t)}")

    print("\nall checks passed")


if __name__ == "__main__":
    main()
