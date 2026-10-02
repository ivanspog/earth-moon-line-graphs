#!/usr/bin/env python3
"""F-037: the F5 calibration set (frozen .plan/F5-PROBLEM.md) as networkx graphs on 0..n-1,
plus exact mad (max average degree) by Dinkelbach iteration over integer min-cuts.

  (a) tight:      K5 v C8^2 (biplanar, 9);  K1 v C16(1,2,6,7,8) (= K1 v C8^2 x K2, C-h8, 9)
  (b) counts:     the 22 open line graphs of F-032/F-033 (A4 set) + the palette graph P (28/3)
  (c) count-dead: C7 x K4 (28/3), C5[3,3,5,3,5], C5[3,4,4,3,5] (19/2)
  (d) near-extr.: Sulanke K6 v C5 (17/2)
"""
import itertools, os, sys
from fractions import Fraction as Fr
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def circulant(m, D):
    G = nx.Graph(); G.add_nodes_from(range(m))
    for i in range(m):
        for d in D:
            G.add_edge(i, (i + d) % m)
    return G


def join(G1, G2):
    G = nx.disjoint_union(G1, G2)
    n1 = G1.number_of_nodes()
    G.add_edges_from((u, n1 + v) for u in range(n1) for v in range(G2.number_of_nodes()))
    return G


def blowup_cycle(w):
    off = [sum(w[:i]) for i in range(len(w))]
    G = nx.Graph(); G.add_nodes_from(range(sum(w)))
    bag = lambda i: range(off[i], off[i] + w[i])
    for i in range(len(w)):
        G.add_edges_from(itertools.combinations(bag(i), 2))
        G.add_edges_from((u, v) for u in bag(i) for v in bag((i + 1) % len(w)))
    return G


def palette():
    from f033_fractional_certificates import palette as pal
    n, E = pal()
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
    return G


def line_graphs():
    from f034_a4_line_graph_sat import open_members, build
    out = []
    for slack, e, mults, m in open_members():
        n, E = build(m)[:2]
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
        out.append((f"L(M) e={e} slack={slack} [{mults}]", G))
    return out


def calibration(include_b=True):
    cs = [("(a) K5 v C8^2", join(nx.complete_graph(5), circulant(8, [1, 2]))),
          ("(a) K1 v C16(1,2,6,7,8)", join(nx.complete_graph(1), circulant(16, [1, 2, 6, 7, 8])))]
    if include_b:
        cs += [("(b) " + t, G) for t, G in line_graphs()]
        cs += [("(b) P (palette)", palette())]
    cs += [("(c) C7 x K4", blowup_cycle([4] * 7)),
           ("(c) C5[3,3,5,3,5]", blowup_cycle([3, 3, 5, 3, 5])),
           ("(c) C5[3,4,4,3,5]", blowup_cycle([3, 4, 4, 3, 5])),
           ("(d) K6 v C5 (Sulanke)", join(nx.complete_graph(6), nx.cycle_graph(5)))]
    return [(t, nx.convert_node_labels_to_integers(G)) for t, G in cs]


def densest(G):
    """Exact max_S e(S)/|S| (a Fraction) and a maximiser S."""
    V = list(G.nodes()); E = list(G.edges())
    if not E:
        return Fr(0), set(V[:1])
    g = Fr(len(E), len(V)); S = set(V)
    while True:
        p, q = g.numerator, g.denominator
        F = nx.DiGraph()
        big = 10 ** 12
        for i, (u, v) in enumerate(E):
            F.add_edge("s", ("e", i), capacity=q)
            F.add_edge(("e", i), ("v", u), capacity=big)
            F.add_edge(("e", i), ("v", v), capacity=big)
        for v in V:
            F.add_edge(("v", v), "t", capacity=p)
        cut, (src_side, _) = nx.minimum_cut(F, "s", "t")
        val = len(E) * q - cut          # = max_S (q e(S) - p |S|)
        if val <= 0:
            return g, S
        S2 = {x[1] for x in src_side if isinstance(x, tuple) and x[0] == "v"}
        eS = G.subgraph(S2).number_of_edges()
        g, S = Fr(eS, len(S2)), S2


def mad(G):
    return 2 * densest(G)[0]


if __name__ == "__main__":
    for t, G in calibration():
        print(t, G.number_of_nodes(), G.number_of_edges(), "mad", mad(G))
