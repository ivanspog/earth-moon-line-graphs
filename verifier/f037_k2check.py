#!/usr/bin/env python3
# Fact (F5) of P-008 (used in Lemma A3): written during adversarial review of P-008 and re-run
# independently: 139 + 18 = 157 classes, all DEAD, in about 80 s.
"""Referee: close the |S| = 5 branch of Theorem A(ii) WITHOUT Szeider's theorem.

Branch: odd S, |S| = 5, e_H(S) >= 19, Delta(H) <= 8 (so e(S) <= 20), every triple sum <= 8,
L(H[S]) biplanar (induced subgraph).  Enumerate all loopless 5-vertex multigraphs with
19 or 20 edges, Delta <= 8, triple sums <= 8, up to isomorphism, and kill each by
  (a) hereditary Euler on L(M[S']) for S' subset of the 5 vertices, or
  (b) the triangle-free count on L(M) (max triangle-free subgraph by RC2, witness verified).
Also record: n(L) = 20 => P-003 (alpha <= 2 & biplanar => n <= 19) kills it regardless.
Also: pairwise non-isomorphism of the 22 A4 line graphs.
"""
import itertools, json, time
import networkx as nx
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

P5 = list(itertools.combinations(range(5), 2))


def line_graph(m, S=None):
    lab = [(e, c) for e, x in sorted(m.items()) for c in range(x)
           if S is None or (e[0] in S and e[1] in S)]
    G = nx.Graph(); G.add_nodes_from(range(len(lab)))
    for i, j in itertools.combinations(range(len(lab)), 2):
        if set(lab[i][0]) & set(lab[j][0]):
            G.add_edge(i, j)
    return G


def max_trifree(G):
    E = sorted(tuple(sorted(e)) for e in G.edges())
    idx = {e: i + 1 for i, e in enumerate(E)}
    w = WCNF()
    for a, b, c in itertools.combinations(sorted(G.nodes()), 3):
        if G.has_edge(a, b) and G.has_edge(a, c) and G.has_edge(b, c):
            w.append([-idx[(a, b)], -idx[(a, c)], -idx[(b, c)]])
    for e in E:
        w.append([idx[e]], weight=1)
    with RC2(w) as rc2:
        model = rc2.compute()
        T = [E[i - 1] for i in model if 0 < i <= len(E)]
    H = nx.Graph(T)
    assert all(G.has_edge(*e) for e in T) and sum(nx.triangles(H).values()) == 0
    return len(T)


def canon5(m):
    best = None
    for p in itertools.permutations(range(5)):
        t = tuple(m.get(tuple(sorted((p[i], p[j]))), 0) for i, j in P5)
        if best is None or t < best:
            best = t
    return best


for total in (19, 20):
    classes = {}
    def rec(i, m, left):
        if i == len(P5):
            if left:
                return
            deg = [sum(m[e] for e in P5 if v in e) for v in range(5)]
            if max(deg) > 8:
                return
            if any(m[(a, b)] + m[(a, c)] + m[(b, c)] > 8 for a, b, c in itertools.combinations(range(5), 3)):
                return
            classes[canon5(m)] = 1
            return
        for x in range(0, min(8, left) + 1):
            m[P5[i]] = x
            rec(i + 1, m, left - x)
        m[P5[i]] = 0
    rec(0, {e: 0 for e in P5}, total)
    print(f"e(S) = {total}: {len(classes)} isomorphism classes (Delta<=8, triple sums<=8)")
    for c in sorted(classes):
        m = {P5[k]: c[k] for k in range(10) if c[k]}
        G = line_graph(m)
        n, e = G.number_of_nodes(), G.number_of_edges()
        why = []
        if e > 6 * n - 12:
            why.append(f"Euler {e}>{6*n-12}")
        for k in (3, 4):
            for S in itertools.combinations(range(5), k):
                Gs = line_graph(m, set(S)); ns, es = Gs.number_of_nodes(), Gs.number_of_edges()
                if ns >= 3 and es > 6 * ns - 12:
                    why.append(f"hered-Euler S={S} {es}>{6*ns-12}"); break
            if why: break
        tf = max_trifree(G)
        if tf > 4 * n - 8:
            why.append(f"trifree {tf}>{4*n-8}")
        if n == 20:
            why.append("P-003 (alpha<=2, n=20>19)")
        mult = " ".join(f"{a}{b}:{c[k]}" for k, (a, b) in enumerate(P5) if c[k])
        print(f"   {mult:38s} n={n} e={e}  {'DEAD: ' + '; '.join(why) if why else '*** SURVIVES ***'}")

# pairwise non-isomorphism of the 22
import os
HERE = os.path.dirname(os.path.abspath(__file__)) + "/"
Ls = []
for row in open(HERE + "a4_list.txt"):
    toks = row.split()
    m = {(int(t[0]), int(t[1])): int(t.split(":")[1]) for t in toks[3:]}
    Ls.append(line_graph(m))
iso_pairs = [(i, j) for i, j in itertools.combinations(range(len(Ls)), 2)
             if nx.weisfeiler_lehman_graph_hash(Ls[i]) == nx.weisfeiler_lehman_graph_hash(Ls[j])
             and nx.is_isomorphic(Ls[i], Ls[j])]
print(f"\n22 A4 line graphs: isomorphic pairs = {iso_pairs} (expect none)")
