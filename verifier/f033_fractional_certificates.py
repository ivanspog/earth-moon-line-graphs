#!/usr/bin/env python3
"""F-033 (a): every chi>=10 candidate this project has tested is forced by the
FRACTIONAL bound, including the "palette" graph P.

For a graph G and vertex weights x >= 0 with x(I) <= 1 for every independent set I,
LP duality gives chi_f(G) >= sum(x), and chi(G) >= ceil(chi_f(G)).  This script
checks such dual certificates EXACTLY (fractions, all maximal independent sets
enumerated), no LP solver needed:

  P (palette, n=26, e=133):  x = 2/3 on A, 1/3 on B and C      -> chi_f >= 28/3 > 9
  C7 x K4 (n=28, e=154):     x = 1/3 everywhere (alpha = 3)     -> chi_f >= 28/3 > 9
  C5[3,3,5,3,5], C5[3,4,4,3,5] (n=19): x = 1/2 (alpha = 2)      -> chi_f >= 19/2 > 9
  G0 = K1 v complement(C5-blowup[4,4,3,3,3]) (n=18): x = 1 on the apex, 1/2 else
                                                                -> chi_f >= 19/2 > 9

(The matching upper bounds -- chi_f(P) = chi_f(C7xK4) = 28/3, 19/2 for the others --
were measured by LP (scipy/HiGHS) in the 2026-09-24 review; only the lower bounds
matter for the classification: chi_f > 9 means ceil(chi_f) >= 10, i.e. the tenth
colour is a weighted-counting fact.)

Run: .venv/bin/python verifier/f033_fractional_certificates.py
"""
import itertools
from fractions import Fraction as Fr


def maximal_independent_sets(n, adj):
    """Bron-Kerbosch on the complement: every maximal independent set, once."""
    out = []

    def rec(R, P, X):
        if not P and not X:
            out.append(R)
            return
        for v in list(P):
            non = lambda S: {u for u in S if u != v and u not in adj[v]}
            rec(R + [v], non(P), non(X))
            P = P - {v}
            X = X | {v}

    rec([], set(range(n)), set())
    return out


def check(name, n, edges, weight):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    sets = maximal_independent_sets(n, adj)
    worst = max(sum(weight(v) for v in s) for s in sets)
    total = sum(weight(v) for v in range(n))
    assert worst <= 1, (name, worst)
    alpha = max(len(s) for s in sets)
    print(f"{name}: n={n} e={len(edges)} alpha={alpha} #maximal-IS={len(sets)} "
          f"max x(I)={worst}  =>  chi_f >= {total} = {float(total):.4f}"
          f"{'  > 9' if total > 9 else ''}")
    return total


def palette():
    A, B = [0, 1], [[2, 3], [4, 5], [6, 7]]
    C = [list(range(8, 14)), list(range(14, 20)), list(range(20, 26))]
    E = set()
    for vs in (A, B[0] + B[1] + B[2], *C):
        E |= set(itertools.combinations(sorted(vs), 2))
    for i in range(3):
        for c in C[i]:
            for w in A + B[i]:
                E.add((min(c, w), max(c, w)))
    return 26, sorted(E)


def inflation(w):
    off = [sum(w[:i]) for i in range(len(w))]
    bag = lambda i: range(off[i], off[i] + w[i])
    E = set()
    for i in range(len(w)):
        E |= set(itertools.combinations(bag(i), 2))
        for u in bag(i):
            for v in bag((i + 1) % len(w)):
                E.add((min(u, v), max(u, v)))
    return sum(w), sorted(E)


def cone_over_complement_blowup(w):
    off = [sum(w[:i]) for i in range(5)]
    bag = lambda i: range(off[i], off[i] + w[i])
    F = {(min(u, v), max(u, v)) for i in range(5) for u in bag(i) for v in bag((i + 1) % 5)}
    m = sum(w)
    E = {e for e in itertools.combinations(range(m), 2) if e not in F}
    E |= {(u, m) for u in range(m)}
    return m + 1, sorted(E)


if __name__ == "__main__":
    n, E = palette()
    check("P (palette)", n, E, lambda v: Fr(2, 3) if v < 2 else Fr(1, 3))
    n, E = inflation([4] * 7)
    check("C7xK4", n, E, lambda v: Fr(1, 3))
    for w in ([3, 3, 5, 3, 5], [3, 4, 4, 3, 5]):
        n, E = inflation(w)
        check(f"C5{w}", n, E, lambda v: Fr(1, 2))
    n, E = cone_over_complement_blowup([4, 4, 3, 3, 3])
    check("G0", n, E, lambda v: Fr(1) if v == 17 else Fr(1, 2))
