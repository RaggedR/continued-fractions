"""Sturmian sequences of slope sqrt(n) - floor(sqrt(n)), and their derived sequences.

Prints everything that goes into sturmian.tex, so the document quotes computed
values rather than hand-copied ones.
"""
from fractions import Fraction
from math import isqrt
import itertools


def cf_sqrt(n, terms):
    """Partial quotients of sqrt(n): a0, then a1, a2, ... repeating."""
    a0 = isqrt(n)
    out = [a0]
    P, Q = a0, n - a0 * a0
    while len(out) <= terms:
        a = (a0 + P) // Q
        out.append(a)
        P = a * Q - P
        Q = (n - P * P) // Q
    return out


def period(n):
    """The period L of sqrt(n), and the block a_1 .. a_L (which ends in 2a0)."""
    a0 = isqrt(n)
    cf = cf_sqrt(n, 200)
    L = next(i for i in range(1, len(cf)) if cf[i] == 2 * a0)
    assert cf[L + 1:2 * L + 1] == cf[1:L + 1], "period detection failed"
    return L, cf[1:L + 1]


def mechanical(alpha, N):
    """l_k = floor((k+1)a) - floor(k a), computed exactly from a rational cut."""
    return [int((k + 1) * alpha) - int(k * alpha) for k in range(N)]


def approx(n, depth):
    """A rational just below alpha = sqrt(n)-a0, accurate enough for N letters."""
    cf = cf_sqrt(n, depth)
    x = Fraction(cf[-1])
    for a in reversed(cf[1:-1]):
        x = a + 1 / x
    return 1 / x                      # [0; a1, a2, ...]


def complexity(s, m):
    return len({tuple(s[i:i + m]) for i in range(len(s) - m + 1)})


def gaps(s):
    """Steps between consecutive 1s. These take exactly two values, a and a+1,
    where a = floor(1/alpha)."""
    idx = [i for i, c in enumerate(s) if c == 1]
    return [idx[j + 1] - idx[j] for j in range(len(idx) - 1)]


def derive(s):
    """One letter per gap between consecutive 1s: long gap -> 1, short -> 0.
    The long gap has frequency G(alpha), so this is the Sturmian sequence of
    slope G(alpha)."""
    g = gaps(s)
    lo, hi = min(g), max(g)
    assert hi - lo == 1, f"gap lengths {sorted(set(g))} not consecutive"
    return [1 if x == hi else 0 for x in g]


def show(s, k=40):
    return "".join(map(str, s[:k]))


for n in (2, 7):
    a0 = isqrt(n)
    L, blk = period(n)
    alpha = approx(n, 80)
    s = mechanical(alpha, 60000)
    print(f"\n=== n = {n}   sqrt(n) = [{a0}; {','.join(map(str, blk))}]  L = {L}")
    print(f"alpha = sqrt({n}) - {a0} = [0; {','.join(map(str, blk))}, ...]")
    print(f"  F(m) for m=1..6: {[complexity(s, m) for m in range(1, 7)]}")
    print(f"  l = {show(s)}")
    cur, a = s, alpha
    for step in range(1, L + 1):
        cur = derive(cur)
        a = 1 / a - int(1 / a)
        print(f"  derive^{step}: slope {float(a):.6f}  density {sum(cur)/len(cur):.6f}"
              f"  F(m)={[complexity(cur, m) for m in range(1, 5)]}")
        print(f"             {show(cur)}")
    print(f"  back to alpha = {float(alpha):.6f} after {L} steps:"
          f" {abs(float(a) - float(alpha)) < 1e-9}")
