"""Verify Theorem 1 directly: the block of sqrt(n) closes with 2a0 and the
rest is a palindrome.  Checked for every non-square n below the bound."""
import math, sys
def block(n, a0):
    P, Q = 0, 1
    a = (a0+P)//Q; P = a*Q-P; Q = (n-P*P)//Q      # consume a0
    out = []
    while True:
        a = (a0+P)//Q; out.append(a)
        P = a*Q-P; Q = (n-P*P)//Q
        if Q == 1:
            out.append((a0+P)//Q); return out
N = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
bad = 0; tested = 0
for n in range(2, N):
    a0 = math.isqrt(n)
    if a0*a0 == n: continue
    b = block(n, a0); tested += 1
    if b[-1] != 2*a0 or b[:-1] != b[:-1][::-1]:
        bad += 1
        if bad < 5: print("  FAIL", n, b)
print(f"non-squares tested below {N:,}: {tested:,}   failures: {bad}")
