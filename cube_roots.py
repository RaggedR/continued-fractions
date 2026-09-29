"""
Everything computed for cube-roots.tex.

  1. continued fractions of cbrt(n) -- no period, heavy Gauss-Kuzmin tail
  2. the cubic Pell equation  x^3 + n y^3 + n^2 z^3 - 3 n x y z = 1
  3. Jacobi-Perron on (cbrt(n), cbrt(n)^2)
  4. the square-root expansions, and their rate of convergence
"""
import math
from mpmath import mp, mpf, sqrt, cbrt, floor, log10, findroot
mp.dps = 120

def cf(x, terms=30):
    out = []
    for _ in range(terms):
        a = int(floor(x)); out.append(a); x = 1/(x - a)
    return out

def cubic_pell(n, bound=12):
    """solutions of the norm form = 1 with small coefficients"""
    s = [(x,y,z)
         for x in range(-bound, bound+1)
         for y in range(-bound, bound+1)
         for z in range(-bound, bound+1)
         if (x,y,z) != (0,0,0)
         and x**3 + n*y**3 + n*n*z**3 - 3*n*x*y*z == 1]
    return sorted(s, key=lambda t: sum(map(abs, t)))

def jpa(n, steps=24):
    """Jacobi-Perron started at (cbrt n, cbrt n squared)"""
    a, b = cbrt(mpf(n)), cbrt(mpf(n))**2
    out = []
    for _ in range(steps):
        ai, bi = int(floor(a)), int(floor(b))
        out.append((ai, bi))
        fa = a - ai
        if fa == 0: break
        a, b = (b - bi)/fa, 1/fa
    return out

if __name__ == "__main__":
    print("1. CONTINUED FRACTIONS  (compare sqrt(2) = [1; 2,2,2,...])")
    for n in (2,3,5,7):
        print(f"   cbrt({n}): {cf(cbrt(mpf(n)))}")

    print("\n2. CUBIC PELL  x^3 + n y^3 + n^2 z^3 - 3 n x y z = 1")
    for n in (2,3,7):
        s = [t for t in cubic_pell(n) if t != (1,0,0)][:2]
        print(f"   n={n}: {s}")
    print("   n=2: (-1,1,0)(1,1,1) are inverse, which is (x-1)(1+x+x^2)=x^3-1 at x=cbrt(2)")

    print("\n3. JACOBI-PERRON on (cbrt n, cbrt n^2)")
    for n in (2,3,7):
        print(f"   n={n}: {jpa(n, 12)}")

    print("\n4. SQUARE-ROOT EXPANSIONS")
    for n in (2,3,10):
        t = cbrt(mpf(n)); x = mpf(1)
        for _ in range(200): x = sqrt(n/x)
        print(f"   sqrt(n/sqrt(n/...)) for n={n:>2}: agrees with cbrt to 60 dp: "
              f"{abs(x-t) < mpf(10)**-60}")
    for m in (1,2,3):
        x = mpf(1.5)
        for _ in range(200): x = sqrt(m + 1/x)
        r = findroot(lambda y: y**3 - m*y - 1, mpf(1.5))
        print(f"   sqrt(m + 1/sqrt(...)) for m={m}: root of x^3-{m}x-1: "
              f"{abs(x-r) < mpf(10)**-50}")
    t = cbrt(mpf(2)); x = mpf(1)
    print("   rate for x -> sqrt(n/x), n=2:")
    for k in range(1, 201):
        x = sqrt(2/x)
        if k in (10, 50, 100, 200):
            print(f"      {k:>3} steps -> {float(-log10(abs(x-t))):5.1f} correct digits")
    print(f"   predicted {float(log10(2)):.4f} digits per step (multiplier -1/2)")
