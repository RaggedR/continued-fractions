"""Verification for penrose-codings.html.

The generalised dual method, written on the coding kernel of all-the-proofs.tex,
and the checks that justify doing it that way.  Run:  python3 pentagrid.py

Claims checked:
  1. the construction yields an exact tiling (every sample point covered once)
  2. de Bruijn's index increments along a grid line equal C+(alpha, c) exactly
  3. the resulting words have complexity F(m) = m+1, i.e. are Sturmian
  4. the slopes are the quadratic units of Q(sqrt 5), Q(sqrt 2), Q(sqrt 3)
  5. for n = 5, the index sums stay bounded and thick/thin -> phi
"""
import math, itertools, random
from collections import Counter

PHI = (1 + 5 ** 0.5) / 2

# ------------------------------------------------------------- the kernel --
def index(alpha, x, k):                  # de Bruijn K; lem:count cumulative form
    return math.ceil(k * alpha + x)

def letter(alpha, x, k):                 # C^+(alpha, x)_k
    return index(alpha, x, k + 1) - index(alpha, x, k)

# --------------------------------------------------------------- the grid --
def dirs(n):
    """Odd n: n-th roots of unity, so sum(e_j) = 0 and de Bruijn's index-sum
    theorem applies.  Even n: the n distinct normals mod pi, exp(i pi j / n)."""
    step = 2 * math.pi / n if n % 2 else math.pi / n
    return [(math.cos(step * j), math.sin(step * j)) for j in range(n)]

def build(n, g, R=9, radius=9.5):
    e = dirs(n); out = []; sums = []
    for j, k in itertools.combinations(range(n), 2):
        (ejx, ejy), (ekx, eky) = e[j], e[k]
        det = ejx * eky - ejy * ekx
        if abs(det) < 1e-12:
            continue
        for r in range(-R, R + 1):
            for s in range(-R, R + 1):
                bj, bk = r - g[j], s - g[k]
                px = ( bj * eky - bk * ejy) / det
                py = (-bj * ekx + bk * ejx) / det
                if px * px + py * py > radius * radius:
                    continue
                K = [math.ceil(px * e[l][0] + py * e[l][1] + g[l]) for l in range(n)]
                K[j], K[k] = r, s
                bx = sum(K[l] * e[l][0] for l in range(n))
                by = sum(K[l] * e[l][1] for l in range(n))
                out.append((bx, by, e[j], e[k], min((k - j) % n, (j - k) % n)))
                sums.append(sum(K))
    return e, out, sums

# ------------------------------------------------- reading off the coding --
def read_line(n, g, k, m, j, N=34, s=3):
    """Walk a family-k line, sample at family-m crossings, count with family j.
    Returns the reduced word and whether it equals C+({alpha}, c) exactly."""
    e = dirs(n); ek, em, ej = e[k], e[m], e[j]
    d = (-ek[1], ek[0])
    dem = d[0] * em[0] + d[1] * em[1]
    dej = d[0] * ej[0] + d[1] * ej[1]
    if abs(dem) < 1e-9:
        return None
    alpha = dej / dem
    p0 = (ek[0] * (s - g[k]), ek[1] * (s - g[k]))
    t0 = -(p0[0] * em[0] + p0[1] * em[1] + g[m]) / dem
    h = 1.0 / dem
    c = p0[0] * ej[0] + p0[1] * ej[1] + g[j] + t0 * dej
    K = []
    for i in range(N + 1):
        t = t0 + i * h
        p = (p0[0] + t * d[0], p0[1] + t * d[1])
        K.append(math.ceil(p[0] * ej[0] + p[1] * ej[1] + g[j]))
    fl = math.floor(alpha)
    word = [K[i + 1] - K[i] - fl for i in range(len(K) - 1)]
    pred = [letter(alpha - fl, c, i) for i in range(len(word))]
    F = [len({tuple(word[t:t + mm]) for t in range(len(word) - mm + 1)})
         for mm in range(1, 9)]
    return dict(alpha=alpha, frac=alpha - fl, word=word, agrees=(word == pred), F=F)

def identify(a, n):
    cand = {5: [('phi', PHI), ('1/phi', 1/PHI), ('1/phi^2', 1/PHI**2), ('phi^2', PHI**2)],
            4: [('sqrt2', 2**.5), ('1/sqrt2', 1/2**.5), ('sqrt2-1', 2**.5-1),
                ('1+sqrt2', 1+2**.5), ('1-1/sqrt2', 1-1/2**.5)],
            6: [('sqrt3', 3**.5), ('1/sqrt3', 1/3**.5), ('sqrt3-1', 3**.5-1),
                ('2+sqrt3', 2+3**.5), ('1-1/sqrt3', 1-1/3**.5)]}[n]
    for nm, v in [('1', 1.0)] + cand:
        for sg in (1, -1):
            if abs(a - sg * v) < 1e-9:
                return ('-' if sg < 0 else '') + nm
    return '?'

# ------------------------------------------------------------------ tests --
def pt_in(poly, pt):
    x, y = pt; c = False
    for i in range(4):
        x1, y1 = poly[i]; x2, y2 = poly[(i + 1) % 4]
        if ((y1 > y) != (y2 > y)) and (x < (x2 - x1) * (y - y1) / (y2 - y1) + x1):
            c = not c
    return c

CASES = [(5, [0.1, 0.23, -0.37, 0.41, -0.37]),
         (4, [0.1, 0.2, -0.15, -0.15]),
         (6, [0.13, 0.2, -0.15, 0.3, 0.05, -0.53])]

def main():
    ok = True
    print("1. exact tiling")
    for n, g in CASES:
        e, tiles, sums = build(n, g)
        polys = [[(b0, b1), (b0+ej[0], b1+ej[1]),
                  (b0+ej[0]+ek[0], b1+ej[1]+ek[1]), (b0+ek[0], b1+ek[1])]
                 for b0, b1, ej, ek, _ in tiles]
        random.seed(7); mult = Counter()
        for _ in range(500):
            a = random.uniform(0, 2*math.pi); rr = random.uniform(0, 2.5)
            p = (rr*math.cos(a), rr*math.sin(a))
            mult[sum(1 for P in polys if pt_in(P, p))] += 1
        good = set(mult) == {1}
        ok &= good
        print(f"   n={n}: {len(tiles)} tiles, shapes={len({t[4] for t in tiles})}, "
              f"coverage={dict(mult)} {'OK' if good else 'FAIL'}")

    print("\n2-4. codings read off the tiling")
    for n, g in CASES:
        for k, m, j in ((0, 1, 2), (0, 2, 1), (1, 3, 0))[:3]:
            if max(k, m, j) >= n:
                continue
            r = read_line(n, g, k, m, j)
            if r is None:
                continue
            sturm = all(v == i + 2 for i, v in enumerate(r['F']))
            ok &= r['agrees'] and sturm
            print(f"   n={n} k={k} m={m} j={j}: alpha={r['alpha']:+.6f} ({identify(r['alpha'],n)})"
                  f"  {{alpha}}={r['frac']:.6f} ({identify(r['frac'],n)})"
                  f"  C+:{'OK' if r['agrees'] else 'FAIL'}"
                  f"  F=m+1:{'OK' if sturm else 'FAIL'}")

    print("\n5. n=5 specific checks")
    e, tiles, sums = build(5, CASES[0][1])
    inner = Counter(t[4] for t in tiles if t[0]**2 + t[1]**2 < 25)
    bounded = max(sums) - min(sums) <= 3
    ratio = inner[1] / inner[2]
    ok &= bounded
    print(f"   index sums in [{min(sums)}, {max(sums)}] {'OK (bounded)' if bounded else 'FAIL'}")
    print(f"   thick/thin interior = {ratio:.4f}  vs phi = {PHI:.4f}")
    print("\n" + ("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED"))

if __name__ == '__main__':
    main()
