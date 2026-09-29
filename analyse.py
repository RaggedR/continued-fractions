"""
The distribution of L(n)/sqrt(n), decomposed.

    L(n)/sqrt(n)  =  [ L(n)/R(n) ]  x  [ R(n)/sqrt(n) ]

The first factor is dynamics: by Gauss-Kuzmin the complete quotients of a
typical continued fraction are equidistributed with respect to the Gauss
measure, and the mean of log(alpha) under that measure is the Levy constant
lambda = pi^2/(12 log 2).  So R = sum of L logs should be about lambda*L, and
L/R should concentrate at 1/lambda regardless of n.

The second factor is arithmetic: the class number formula for the real
quadratic field of discriminant D says h*R = sqrt(D)*L(1,chi), so R/sqrt(n) is
essentially L(1,chi_n)/h(n) -- an L-value divided by a class number.

If the first factor really is near-constant, then the shape of L(n)/sqrt(n) is
not a fact about continued fractions at all.  It is the distribution of
L(1,chi)/h, rescaled.
"""
import math, numpy as np

d = np.load("data/periods.npz")
n, L, R = d["n"], d["L"], d["R"].astype(np.float64)
t = L / np.sqrt(n)                      # the variable in period-distribution.pdf
LAMBDA = math.pi**2 / (12*math.log(2))

print(f"Levy constant lambda = {LAMBDA:.6f}   1/lambda = {1/LAMBDA:.6f}")

print("\nFACTOR 1  --  L(n)/R(n), the dynamical part")
ratio = L / R
for lo, hi in [(2,1000), (1000,10000), (10000,50000), (50000,100000)]:
    m = (n >= lo) & (n < hi)
    print(f"  n in [{lo:>6,},{hi:>7,})   mean {ratio[m].mean():.4f}"
          f"   sd {ratio[m].std():.4f}   median {np.median(ratio[m]):.4f}")
big = n >= 10000
print(f"  relative sd over n>10^4: {ratio[big].std()/ratio[big].mean():.4f}")

print("\nFACTOR 2  --  R(n)/sqrt(n), the arithmetic part")
u = R / np.sqrt(n)
for lo, hi in [(2,1000), (1000,10000), (10000,50000), (50000,100000)]:
    m = (n >= lo) & (n < hi)
    print(f"  n in [{lo:>6,},{hi:>7,})   mean {u[m].mean():.4f}"
          f"   sd {u[m].std():.4f}   max {u[m].max():.4f}")

print("\nIS L/sqrt(n) EXPONENTIAL?  (exponential <=> constant hazard)")
edges = np.linspace(0, 2.6, 21)
hist, _ = np.histogram(t, bins=edges)
surv = len(t) - np.concatenate(([0], np.cumsum(hist)))[:-1]
w = edges[1]-edges[0]
print("    t        count   survivors    hazard f/(P>t)")
for i in range(14):
    hz = hist[i]/(surv[i]*w) if surv[i] else float('nan')
    print(f"  {edges[i]:.2f}-{edges[i+1]:.2f}  {hist[i]:>7,}   {surv[i]:>8,}      {hz:.3f}")

print("\nPARITY  (odd period <=> x^2-ny^2=-1 solvable)")
for M in (1000, 10000, 100000):
    m = n < M
    print(f"  n < {M:>7,}:  odd {(L[m]%2==1).sum():>6,} / {m.sum():>6,}"
          f"  = {(L[m]%2==1).mean()*100:5.2f}%")

print("\nMEAN GROWTH")
for M in (3000, 10000, 30000, 100000):
    m = n < M
    mean = L[m].mean(); s = math.sqrt(M)
    print(f"  M={M:>7,}  mean L {mean:8.2f}   mean/sqrt(M) {mean/s:.4f}"
          f"   x log M {mean*math.log(M)/s:.4f}   x sqrt(log M) {mean*math.sqrt(math.log(M))/s:.4f}")

np.savez_compressed("data/derived.npz", t=t, ratio=ratio, u=u)
