"""
Does the Weibull residual shrink because the fit is right, or does it stop?

Split the bin-by-bin residual into the part sampling error can explain and the
part it cannot.  For each bin the fitted model predicts probability p, so the
count has binomial standard deviation sqrt(N p (1-p)); dividing by N*width puts
it in density units.  Then

    rms(resid)^2  ~  noise^2 + systematic^2

If the Weibull were the true law the residual would track the noise column and
the standardised residual would sit near 1 at every M.
"""
import math, numpy as np
from scipy import stats
from wfit import weibull_mle

d = np.load("data/periods_1e6.npz"); n, L = d["n"], d["L"]
t_all = L/np.sqrt(n)
E = np.linspace(0, 2.8, 57); w = E[1]-E[0]

print(f"{'M':>10}{'N':>9}{'rms resid':>11}{'noise only':>12}{'excess':>9}{'rms standardised':>19}")
for M in [10_000, 31_623, 100_000, 316_228, 1_000_000]:
    t = t_all[n < M]; N = len(t)
    k, sc = weibull_mle(t)
    cnt, _ = np.histogram(t, bins=E)
    p = np.diff(stats.weibull_min.cdf(E, k, 0, sc))
    resid = cnt/(N*w) - p/w
    se = np.sqrt(np.maximum(N*p*(1-p), 1))/(N*w)
    rms = math.sqrt((resid**2).mean()); noise = math.sqrt((se**2).mean())
    print(f"{M:>10,}{N:>9,}{rms:>11.4f}{noise:>12.4f}"
          f"{math.sqrt(max(rms**2-noise**2,0)):>9.4f}{math.sqrt(((resid/se)**2).mean()):>19.2f}")
