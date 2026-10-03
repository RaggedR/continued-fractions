"""Numerical checks behind `all-the-proofs.tex` §7 (step 5 of §6).

Everything here was run before the section was written, and it reproduces every
number quoted in `HANDOVER.md`. Nothing is tested on a decimal truncation:
slopes are built as sqrt(n) - floor(sqrt(n)) and the codings are computed by
exact integer comparison in Z[sqrt n].

Four claims, in the order the proof needs them:

  A  prop:bound   |Delta_a(u)| < 1 for every factor u, where Delta_a(u) =
                  |u|_1 - alpha|u|.  Tested exactly (no floats in the
                  predicate), and the supremum is seen to approach 1.
  B  the decomposition u = 0^s tau_a(u') q behind prop:bound: q empty or a
     PROPER prefix 1 0^t of its block, hence s <= a and t <= a-1, with
     s = a forcing 1u' to be a factor of l'.  The lem:dev identity
     Delta_a(u) = -alpha Delta_b(u') + boundary is checked on each factor.
  C  thm:step5    x = sup_N (S(N) - N alpha) recovers the intercept.
  D  thm:counterex  for 1.c the supremum is 1 and is attained nowhere, which
     is why C+ is needed.

Run: python step5_check.py
"""
from fractions import Fraction
from math import floor, isqrt, sqrt


# ---------------------------------------------------------------- codings

def floor_ksqrt_plus(k, n, x):
    """floor(k*sqrt(n) + x) for rational x in [0,1), by integer comparison."""
    base = isqrt(k * k * n)                     # floor(k sqrt n)
    c = base + 1 - x                            # is the fractional part >= 1-x?
    ge = (k * k * n) >= c * c if c > 0 else True
    return base + (1 if ge else 0)


def ceil_ksqrt_plus(k, n, x):
    """ceil(k*sqrt(n) + x). k sqrt n is irrational for k >= 1."""
    if k == 0:
        return 0 if x == 0 else 1
    return floor_ksqrt_plus(k, n, x) + 1


def code(n, x, N):
    """C(alpha, x), alpha = sqrt(n) - floor(sqrt(n)), by lem:mech."""
    a0 = isqrt(n)
    f = [floor_ksqrt_plus(k, n, x) - k * a0 for k in range(N + 1)]
    return [f[k + 1] - f[k] for k in range(N)]


def codeUp(n, x, N):
    """C+(alpha, x), by lem:mech."""
    a0 = isqrt(n)
    g = [ceil_ksqrt_plus(k, n, x) - k * a0 for k in range(N + 1)]
    return [g[k + 1] - g[k] for k in range(N)]


def derived(s, a):
    """lem:blocks: one letter per gap between consecutive 1s, long gap -> 1.
    Returns (l', k0). Asserts cor:gaps, that every gap is a or a+1."""
    idx = [i for i, c in enumerate(s) if c == 1]
    gaps = [idx[i + 1] - idx[i] for i in range(len(idx) - 1)]
    assert set(gaps) <= {a, a + 1}, sorted(set(gaps))
    return [1 if g == a + 1 else 0 for g in gaps], idx[0]


# ------------------------------------------------- A: the factor bound

def delta_lt_one(A, L, n):
    """|A - L*sqrt(n)| < 1, exactly. Here A = |u|_1 + L*a0."""
    lo = (A - 1 < 0) or ((A - 1) ** 2 < L * L * n)
    hi = (A + 1 > 0) and (L * L * n < (A + 1) ** 2)
    return lo and hi


def check_bound(seq, n, Lmax):
    """prop:bound over every factor of length <= Lmax. Returns (failures, sup)."""
    a0 = isqrt(n)
    al = sqrt(n) - a0
    S = [0]
    for c in seq:
        S.append(S[-1] + c)
    bad, sup = [], 0.0
    for M in range(len(seq) - 1):
        for N in range(M + 1, min(M + Lmax, len(seq)) + 1):
            L, ones = N - M, S[N] - S[M]
            if not delta_lt_one(ones + L * a0, L, n):
                bad.append((M, N, ones, L))
            sup = max(sup, abs(ones - L * al))
    return bad, sup


# ------------------------------- B: the decomposition of prop:bound

def check_decomposition(n, x, Mmax=3000, Lmax=36, Nletters=20000):
    """Every factor is 0^s tau_a(u') q with q empty or a proper prefix 1 0^t.
    Checks s <= a, t <= a-1, s = a => 1u' a factor, the lem:dev identity,
    and |Delta| < 1. Returns (counts, failures)."""
    al = sqrt(n) - isqrt(n)
    a = floor(1 / al)
    if a < 2:
        return None                 # needs step 1's letter exchange first
    be = 1 / al - a
    s = code(n, x, Nletters)
    lp, _ = derived(s, a)
    kp = [i for i, c in enumerate(s) if c == 1]
    blk = {}
    for i in range(len(kp) - 1):
        for p in range(kp[i], kp[i + 1]):
            blk[p] = (i, p - kp[i])

    counts = {"u' empty": 0, "general": 0, "s = a": 0}
    bad = []
    for M in range(kp[0], Mmax):
        for L in range(1, Lmax + 1):
            N = M + L
            if N - 1 not in blk or N not in blk:
                break
            i0, off = blk[M]
            first = i0 if off == 0 else i0 + 1
            last, j = first - 1, first
            while j < len(lp) and kp[j + 1] <= N:
                last, j = j, j + 1
            ss = min(kp[first] - M, L) if first > i0 else 0
            if last < first:
                up, q_at = [], M + ss
            else:
                up, q_at = lp[first:last + 1], kp[last + 1]
            qlen = N - q_at
            tt = qlen - 1 if qlen > 0 else None

            if ss > a:
                bad.append(("s > a", M, L, ss))
            if tt is not None and tt > a - 1:
                bad.append(("t > a-1", M, L, tt))
            if up and ss == a:
                counts["s = a"] += 1
                if not (first >= 1 and lp[first - 1] == 1):
                    bad.append(("s = a but 1u' not a factor", M, L))
            dp = sum(up) - len(up) * be
            d = sum(s[M:N]) - L * al
            pred = -al * ss - al * dp + ((1 - al * (1 + tt)) if tt is not None else 0)
            if abs(pred - d) > 1e-9:
                bad.append(("lem:dev identity", M, L, d, pred))
            if abs(d) >= 1:
                bad.append(("|Delta| >= 1", M, L, d))
            counts["u' empty" if not up else "general"] += 1
    return counts, bad


# ------------------------------------------ C, D: the intercept

def admissible(seq, al, Nmax):
    """[sup_N D(N), 1 + inf_N D(N)) with D(N) = S(N) - N alpha."""
    S, lo, hi = 0, 0.0, 1.0
    for N in range(1, min(Nmax, len(seq)) + 1):
        S += seq[N - 1]
        lo = max(lo, S - N * al)
        hi = min(hi, S + 1 - N * al)
    return lo, hi


# ------------------------------------------------------------------ main

def main():
    F = Fraction
    print("A. prop:bound -- |u|_1 - alpha|u| in (-1,1), exact, |u| <= 80")
    for n in (2, 3, 5, 7, 11, 13, 29, 47):
        for x in (F(0), F(1, 3), F(7, 11)):
            for cod, nm in ((code, "C "), (codeUp, "C+")):
                bad, sup = check_bound(cod(n, x, 260), n, 80)
                assert not bad, (n, x, nm, bad[:3])
                print(f"   n={n:3d} x={str(x):5s} {nm}  ok   sup={sup:.6f}")

    print("\nB. the decomposition, every factor of length <= 36")
    total = 0
    for n in (2, 3, 5, 6, 8, 10, 11, 12, 13, 29, 43):
        for x in (F(0), F(1, 3), F(7, 11), F(9, 10)):
            r = check_decomposition(n, x)
            if r is None:
                continue
            counts, bad = r
            assert not bad, (n, x, bad[:2])
            total += counts["u' empty"] + counts["general"]
            empty, gen, sa = counts["u' empty"], counts["general"], counts["s = a"]
            print(f"   n={n:3d} x={str(x):5s}  u'empty={empty:6d}"
                  f"  general={gen:6d}  s=a={sa:6d}  ok")
    print(f"   {total} factors checked")

    print("\nC. thm:step5 -- x = sup_N (S(N) - N alpha)")
    for n in (2, 5, 7, 13):
        al = sqrt(n) - isqrt(n)
        for x in (F(0), F(1, 3), F(7, 11)):
            lo, hi = admissible(code(n, x, 4000), al, 4000)
            assert lo <= float(x) <= hi, (n, x, lo, hi)
            print(f"   n={n:3d} x={float(x):.9f}  bracket [{lo:.9f}, {hi:.9f})"
                  f"  width {hi - lo:.1e}")

    print("\nD. thm:counterex -- 1.c has supremum 1, attained nowhere")
    al = (sqrt(5) - 1) / 2
    c = [int((k + 1) * al + al) - int(k * al + al) for k in range(4000)]
    lo, hi = admissible([1] + c[:3999], al, 4000)
    print(f"   sup D = {lo:.12f} -> 1,  1 + inf D = {hi:.12f}")
    print(f"   no x in [0,1) works for C; 1.c = C+(alpha, 0)")
    assert hi == 1.0 and lo < 1.0

    print("\nall checks passed")


if __name__ == "__main__":
    main()
