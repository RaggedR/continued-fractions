"""
Period of the continued fraction of sqrt(n), and the regulator, for n < N.

The expansion of sqrt(n) is computed by the standard PQa recurrence, which
keeps the surd in exact integer form and never touches a float:

    a0 = floor(sqrt(n)),   P0 = 0,   Q0 = 1

    a_i = floor((a0 + P_i) / Q_i)
    P_{i+1} = a_i Q_i - P_i
    Q_{i+1} = (n - P_{i+1}^2) / Q_i

The state (P_i, Q_i) determines the complete quotient alpha_i = (P_i + sqrt(n))/Q_i.
The expansion is periodic and the period closes at the first i >= 1 with Q_i = 1,
equivalently at the first a_i = 2*a0.  That index is the period length L(n).

The regulator is accumulated along the way.  Over one period the complete
quotients multiply to the fundamental unit of the order Z[sqrt(n)]:

    eps = prod_{i=1}^{L} alpha_i        so   R = log(eps) = sum log(alpha_i)

The product runs from i = 1, not i = 0, so each alpha is read off AFTER the
state has been advanced.  Taking it before instead contributes log(sqrt(n)) as
a spurious first factor.  When L is odd this eps has norm -1 and the smallest
solution of x^2 - n y^2 = +1 is its square, which is why the checks below
double R in that case.

which is a sum of L logarithms of moderate-sized numbers -- numerically stable,
unlike forming eps = x + y sqrt(n) directly, where x and y overflow a float
well before n = 1000.
"""
import math, numpy as np

def period_and_regulator(n, a0):
    P, Q = 0, 1
    L = 0
    R = 0.0
    sq = math.sqrt(n)
    while True:
        a = (a0 + P) // Q
        P = a * Q - P
        Q = (n - P * P) // Q
        R += math.log((P + sq) / Q)      # log alpha_i, AFTER advancing the state
        L += 1
        if Q == 1:
            return L, R

def run(N):
    ns, Ls, Rs = [], [], []
    for n in range(2, N):
        a0 = math.isqrt(n)
        if a0 * a0 == n:                 # perfect squares have no expansion
            continue
        L, R = period_and_regulator(n, a0)
        ns.append(n); Ls.append(L); Rs.append(R)
    return (np.array(ns, dtype=np.int64),
            np.array(Ls, dtype=np.int64),
            np.array(Rs, dtype=np.float64))

if __name__ == "__main__":
    N = 100000
    n, L, R = run(N)
    np.savez_compressed("data/periods.npz", n=n, L=L, R=R, N=N)
    print(f"n from 2 to {N-1}.  {len(n)} non-squares.")
    print(f"shortest {L.min()}   longest {L.max()}   mean {L.mean():.2f}   median {int(np.median(L))}")
    # validation against three fundamental units known in closed form
    for m, x, y in [(2,3,2), (13,649,180), (61,1766319049,226153980)]:
        i = np.searchsorted(n, m)
        want = math.log(x + y*math.sqrt(m))
        got  = R[i] if L[i] % 2 == 0 else 2*R[i]   # odd period: unit has norm -1
        print(f"  check n={m:3d}:  R computed {got:.9f}   from ({x},{y}) {want:.9f}"
              f"   {'OK' if abs(got-want) < 1e-6 else 'MISMATCH'}")
