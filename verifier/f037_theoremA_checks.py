#!/usr/bin/env python3
"""Cheap refutation tests for the lemmas of P-008 Theorem A (A1, A2, A(i) arithmetic).
 A-L1  chi_f(L(H)) = max(Delta(H), max_{odd S,|S|>=3} 2e(S)/(|S|-1))  vs exact LP, random multigraphs
 A-L2  e(L(J)) = sum_v C(d_J(v),2) - sum_uv C(a_uv,2)   (explicit line graph) and inequality (1)
 A-L3/L4 arithmetic: for every odd s in [5, 999] and every m from m0 to r*C(s,2) the Euler
       inequality (1) fails (r = 3 for density > 9, r = 2 for density > 8)
 A-cal the 22 calibration line graphs: root multiplicity >= 4 and an odd set of density 28/3."""
import itertools, random
from fractions import Fraction as Fr
from math import comb
import networkx as nx
from f037_common import chi_f
from f034_a4_line_graph_sat import open_members


def line_graph_of(mult):          # mult: {(a,b): k}
    lab = [(e, c) for e, k in sorted(mult.items()) for c in range(k)]
    G = nx.Graph(); G.add_nodes_from(range(len(lab)))
    for i, j in itertools.combinations(range(len(lab)), 2):
        if set(lab[i][0]) & set(lab[j][0]):
            G.add_edge(i, j)
    return G


def gamma_formula(mult, nv):
    deg = [0] * nv
    for (a, b), k in mult.items():
        deg[a] += k; deg[b] += k
    best = Fr(max(deg))
    for r in range(3, nv + 1, 2):
        for S in itertools.combinations(range(nv), r):
            s = set(S); e = sum(k for (a, b), k in mult.items() if a in s and b in s)
            best = max(best, Fr(2 * e, r - 1))
    return best


rng = random.Random(5)
bad = 0; tested = 0
for _ in range(400):
    nv = rng.randint(3, 6)
    mult = {}
    for a, b in itertools.combinations(range(nv), 2):
        if rng.random() < 0.6:
            mult[(a, b)] = rng.randint(1, 4)
    if not mult or sum(mult.values()) > 16:
        continue
    L = line_graph_of(mult)
    lo, hi, _ = chi_f(L); tested += 1
    f = gamma_formula(mult, nv)
    if not (lo == hi == f):
        bad += 1; print("A-L1 MISMATCH", mult, lo, hi, f)
    # A-L2 identity
    deg = [0] * nv
    for (a, b), k in mult.items():
        deg[a] += k; deg[b] += k
    assert L.number_of_edges() == sum(comb(d, 2) for d in deg) - sum(comb(k, 2) for k in mult.values())
print(f"A-L1: {tested} random multigraph roots, formula == exact LP chi_f in all but {bad}")
print("A-L2: edge-count identity (3) holds on all of them")

for r, dens in ((3, 9), (2, 8)):
    worst = None
    for s in range(5, 1000, 2):
        m0 = dens * (s - 1) // 2 + 1
        for m in range(m0, r * comb(s, 2) + 1):
            val = Fr(2 * m * m, s) - Fr((r + 13) * m, 2) + 12
            if val <= 0:
                print("A-L3/4 FAILS", r, s, m, val); raise SystemExit(1)
            if worst is None or val < worst[0]:
                worst = (val, s, m)
            if m > m0 + 50 and val > 10 ** 6:
                break
    print(f"A-L{3 if r == 3 else 4}: r={r}, density>{dens}: Euler inequality (1) violated for every odd s<1000; "
          f"min residual {worst[0]} at s={worst[1]}, m={worst[2]}")

for slack, e, mults, m in open_members():
    mu = max(m.values())
    g = gamma_formula(m, 7)
    assert mu >= 4 and g == Fr(28, 3), (mults, mu, g)
print("A-cal: all 22 calibration line graphs have root multiplicity >= 4 (so Lemma 3 does not apply) "
      "and Gamma = 28/3 (odd set = all 7 root vertices)")
