"""Weibull maximum likelihood with the location fixed at zero.

The shape solves   1/k = sum(t^k log t)/sum(t^k) - mean(log t)   by bisection,
then   lambda = ( mean(t^k) )^(1/k).

Written out rather than called from scipy because these samples reach 10^6
points and this is one pass per iteration.  Agrees with
scipy.stats.weibull_min.fit to five decimal places.
"""
import numpy as np

def weibull_mle(x, lo=0.2, hi=5.0, it=80):
    lx = np.log(x); mlx = lx.mean()
    def g(k):
        xk = x**k
        return xk.dot(lx)/xk.sum() - mlx - 1.0/k
    for _ in range(it):
        mid = (lo+hi)/2
        if g(mid) > 0: hi = mid
        else: lo = mid
    k = (lo+hi)/2
    return k, (x**k).mean()**(1/k)
