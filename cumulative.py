"""
How the fitted Weibull shape depends on M, the largest n included.

Earlier fits used disjoint bands.  This uses the cumulative sample
{ L(n)/sqrt(n) : 2 <= n < M }, which is what you get if you simply expand
every square root up to M and fit the result.

Weibull MLE, location fixed at 0.  The shape solves

    1/k  =  sum(t^k log t) / sum(t^k)  -  mean(log t)

by bisection, and then lambda = ( mean(t^k) )^(1/k).  Written out rather than
called from scipy because the samples reach 10^6 points and this is one pass
per iteration.
"""
import math, time, json, numpy as np
from scipy import stats
from period import period_and_regulator
from wfit import weibull_mle

def _main():
    N = 1_000_000
    t0 = time.time()
    ns, Ls = [], []
    for n in range(2, N):
        a0 = math.isqrt(n)
        if a0*a0 == n: continue
        L, _ = period_and_regulator(n, a0)
        ns.append(n); Ls.append(L)
    n = np.array(ns, dtype=np.int64); L = np.array(Ls, dtype=np.int32)
    print(f"periods to {N:,} in {time.time()-t0:.0f}s   {len(n):,} non-squares"
          f"   mean L {L.mean():.2f}")
    np.savez_compressed("data/periods_1e6.npz", n=n, L=L)
    t = L/np.sqrt(n)

    # sanity: agree with scipy on one band
    chk = np.load("data/t_300000.npy")
    k_mine, s_mine = weibull_mle(chk)
    k_sp, _, s_sp = stats.weibull_min.fit(chk, floc=0)
    print(f"MLE check on the 300k band:  mine k={k_mine:.6f} scale={s_mine:.6f}"
          f"   scipy k={k_sp:.6f} scale={s_sp:.6f}")

    rows = []
    for M in [int(x) for x in np.logspace(3.5, 6, 21)]:
        x = t[n < M]
        if len(x) < 500: continue
        k, sc = weibull_mle(x)
        ks = stats.kstest(x, "weibull_min", args=(k, 0, sc)).statistic
        rows.append(dict(M=M, N=len(x), mean=float(x.mean()), k=float(k),
                         scale=float(sc), ks=float(ks), crit=1.358/math.sqrt(len(x))))
        print(f"  M={M:>9,}  N={len(x):>8,}  mean {x.mean():.4f}  k {k:.4f}"
              f"  KS {ks:.4f}  crit {rows[-1]['crit']:.4f}")

    M = np.array([r["M"] for r in rows], float); K = np.array([r["k"] for r in rows])
    a, b = np.polyfit(np.log(M), K, 1)
    print(f"\ncumulative:  k = {b:.4f} {a:+.5f} log M     crosses 1 at M = {math.exp((1-b)/a):,.0f}")
    print(f"band-wise was:  k = 1.3197 -0.02897 log n   crossed 1 at n = 61,864")
    json.dump(dict(rows=rows, a=a, b=b), open("data/cumulative.json","w"), indent=1)

if __name__ == "__main__":
    _main()
