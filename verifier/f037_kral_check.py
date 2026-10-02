#!/usr/bin/env python3
"""F-037 / P-009: sanity checks for  alpha(G) >= sum_v 2/(d(v)+c(v)+1)  (Abiad-Kumar-Pragada,
arXiv:2609.00210 Thm 3.1, proving Brause-Randerath-Rautenbach-Schiermeyer 2016) and its biplanar
corollary alpha(G) > 2n/21 (answering Kral', Barbados 2018 Problem 4).
 (a) random graphs n <= 14: exact alpha vs the localized bound (Fractions)
 (b) all calibration graphs + Patil's corpus (whole graphs): alpha, the localized bound, 2n/21
 (c) the known extremal biplanar ratio 2/17 (Sulanke K6 v C5: n = 11, alpha = 2) vs 2/21."""
import glob, os, random, re, sys
from fractions import Fraction as Fr
import networkx as nx
from f037_calib import calibration


def alpha(G):
    return max((len(c) for c in nx.find_cliques(nx.complement(G))), default=0)


def cvert(G, v):
    return 1 + max((len(c) for c in nx.find_cliques(G.subgraph(list(G[v])))), default=0)


def bound(G):
    return sum(Fr(2, G.degree(v) + cvert(G, v) + 1) for v in G)


rng = random.Random(21); bad = 0; N = 0
for _ in range(2000):
    n = rng.randint(4, 14)
    G = nx.gnp_random_graph(n, rng.uniform(0.1, 0.9), seed=rng.randrange(10**9))
    N += 1
    if alpha(G) < bound(G):
        bad += 1; print("VIOLATION", sorted(G.edges()))
print(f"(a) {N} random graphs n<=14: violations of alpha >= sum 2/(d+c+1): {bad}")

rows = [(t, G) for t, G in calibration()]
if len(sys.argv) > 1:
    for f in sorted(glob.glob(os.path.join(sys.argv[1], "**", "*.edges"), recursive=True)):
        if re.search(r"_layer\d*\.edges$", f):
            continue
        G = nx.Graph()
        for line in open(f):
            t = line.split()
            if len(t) >= 2 and t[0].lstrip("-").isdigit() and t[0] != t[1]:
                G.add_edge(int(t[0]), int(t[1]))
        rows.append(("corpus " + os.path.relpath(f, sys.argv[1]), nx.convert_node_labels_to_integers(G)))
worst = None
for t, G in rows:
    n = G.number_of_nodes(); a = alpha(G); b = bound(G)
    assert a >= b, (t, a, b)
    r = Fr(a, n)
    if worst is None or r < worst[0]:
        worst = (r, t, n, a, b)
print(f"(b) {len(rows)} calibration + corpus graphs: alpha >= localized bound in all; "
      f"minimum alpha/n = {worst[0]} ({float(worst[0]):.4f}) at {worst[1]} (n={worst[2]}, alpha={worst[3]}, "
      f"bound={float(worst[4]):.3f}); 2/21 = {2/21:.4f}, 1/12 = {1/12:.4f}")
