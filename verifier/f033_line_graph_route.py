#!/usr/bin/env python3
"""F-033 (b)-(c): the line-graph route of F-032, completed and pruned.

(b) The k=2 branch.  Goldberg-Seymour with Delta(M) <= 8 gives an odd U with
    e(U) >= 9k+1.  For |U| = 5 the sub-multigraph M[U] has 19 or 20 edges and
    L(M[U]) has alpha <= nu(M[U]) <= 2; P-003 kills 20 (n <= 19), so e(U) = 19 and
    L(M[U]) is a 19-vertex, alpha <= 2 graph with chi >= ceil(2*19/4) = 10, and it
    is an (induced) subgraph of G, hence biplanar.  F-032 said this branch "lands
    in the alpha <= 2 pocket (P-003/P-006)"; P-006 covers n = 14..18 only, and
    n = 19 is (Q19), which is OPEN.  The branch is a finite list, enumerated here:
    loopless multigraphs on 5 vertices, 19 edges, Delta <= 8, every triangle
    multiplicity sum <= 8 (no K9 in the line graph), e(L) <= 6*19-12 = 102.

(c) The k=3 list of 56 (verifier/f032_results.json), filtered by the HEREDITARY
    edge bound (every subgraph of a biplanar graph is biplanar, so
    e(L(M[S])) <= 6|E(M[S])| - 12 for every vertex set S of M) -- F-032 applied the
    bound per connected component only -- and by containment of a line graph from
    list (b) whose non-biplanarity is already established.

(d) [added after the novelty re-check] The TRIANGLE-FREE COUNT: a triangle-free planar
    graph on n >= 3 vertices has at most 2n-4 edges, so a triangle-free subgraph of a
    biplanar graph has at most 4n-8 edges (Trivedi 2026, Q. 7.1; Szeider 2026, Sec. 7).
    Decided exactly by SAT: "is there a triangle-free subgraph with > 4n-8 edges?"

Run: .venv/bin/python verifier/f033_line_graph_route.py   (~1 min)
"""
import itertools
import json
import os

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

HERE = os.path.dirname(os.path.abspath(__file__))
P5 = list(itertools.combinations(range(5), 2))
P7 = list(itertools.combinations(range(7), 2))


def line_graph_counts(m, S):
    """(vertices, edges) of L(M[S]) for a multiplicity dict m."""
    deg = {v: 0 for v in S}
    nL = sq = 0
    for (a, b), x in m.items():
        if a in deg and b in deg:
            deg[a] += x
            deg[b] += x
            nL += x
            sq += x * (x - 1) // 2
    return nL, sum(d * (d - 1) // 2 for d in deg.values()) - sq


def line_graph(m):
    lab = [e for e, x in sorted(m.items()) for _ in range(x)]
    E = [(i, j) for i, j in itertools.combinations(range(len(lab)), 2) if set(lab[i]) & set(lab[j])]
    return len(lab), E


def trifree_exceeds(n, E, bound):
    """SAT: does the graph have a triangle-free subgraph with more than `bound` edges?"""
    G = nx.Graph(E)
    idx = {tuple(sorted(e)): i + 1 for i, e in enumerate(E)}
    cls = [[-idx[tuple(sorted(p))] for p in ((a, b), (a, c), (b, c))]
           for a, b, c in itertools.combinations(range(n), 3)
           if G.has_edge(a, b) and G.has_edge(a, c) and G.has_edge(b, c)]
    cls += CardEnc.atleast(list(range(1, len(E) + 1)), bound + 1, top_id=len(E),
                           encoding=EncType.seqcounter).clauses
    with Cadical153(bootstrap_with=cls) as sat:
        return sat.solve()


def canon5(m):
    best = None
    for p in itertools.permutations(range(5)):
        t = tuple(m.get(tuple(sorted((p[i], p[j]))), 0) for i, j in P5)
        if best is None or t < best:
            best = t
    return best


def k2_family():
    sols = {}

    def rec(i, m, left):
        if i == len(P5):
            if left:
                return
            deg = [sum(m[e] for e in P5 if v in e) for v in range(5)]
            if max(deg) > 8:
                return
            if any(m[(a, b)] + m[(a, c)] + m[(b, c)] > 8
                   for a, b, c in itertools.combinations(range(5), 3)):
                return
            nL, eL = line_graph_counts(m, range(5))
            if eL > 6 * nL - 12:
                return
            sols[canon5(m)] = eL
            return
        for x in range(0, min(8, left) + 1):
            m[P5[i]] = x
            rec(i + 1, m, left - x)
        m[P5[i]] = 0

    rec(0, {e: 0 for e in P5}, 19)
    return sols


def cycle_weights(c):
    """Weights around the cycle if the support of canonical tuple c is a 5-cycle."""
    m = {P5[k]: c[k] for k in range(10) if c[k]}
    if len(m) != 5 or any(sum(1 for e in m if v in e) != 2 for v in range(5)):
        return None
    order, prev, cur = [0], None, 0
    while len(order) < 5:
        nxt = [b if a == cur else a for (a, b) in m if cur in (a, b) and (b if a == cur else a) != prev][0]
        order, prev, cur = order + [nxt], cur, nxt
    return [m[tuple(sorted((order[i], order[(i + 1) % 5])))] for i in range(5)]


def dihedral_min(w):
    rots = [w[i:] + w[:i] for i in range(5)]
    return min(rots + [r[::-1] for r in rots])


DEAD_C5 = {  # established non-biplanar odd-cycle inflations (dihedral-normal weights)
    tuple(dihedral_min([3, 3, 5, 3, 5])): "C5[3,3,5,3,5] (LEAN-3)",
    tuple(dihedral_min([3, 4, 4, 3, 5])): "C5[3,4,4,3,5] (LEAN-4)",
    tuple(dihedral_min([3, 4, 4, 4, 4])): "C5[3,4,4,4,4] (KSS 2023, replicated E-8)",
}


def main():
    fam = k2_family()
    names = {}
    print(f"(b) k=2 branch: {len(fam)} classes (5-vertex multigraphs, 19 edges)")
    new_i = 0
    for c, eL in sorted(fam.items(), key=lambda t: (t[1], t[0])):
        w = cycle_weights(c)
        mult = " ".join(f"{a}{b}:{c[k]}" for k, (a, b) in enumerate(P5) if c[k])
        if w is not None:
            tag = DEAD_C5.get(tuple(dihedral_min(w)), f"C5{dihedral_min(w)} (status unknown)")
        else:
            new_i += 1
            mm = {P5[k]: c[k] for k in range(10) if c[k]}
            nL_, EL_ = line_graph(mm)
            dead = trifree_exceeds(nL_, EL_, 4 * nL_ - 8)
            tag = (f"NEW, e(L)={eL}: " + ("DEAD by triangle-free count (> 4n-8 = 68)" if dead
                   else "survives triangle-free count"))
        names[c] = tag
        print(f"    e(L)={eL}  {mult:40s} {tag}")

    members = json.load(open(os.path.join(HERE, "f032_results.json")))
    print(f"\n(c) k=3 list: {len(members)} members from f032_results.json")
    hered_dead, contained, alive = [], [], []
    for r in members:
        m = {P7[j]: r["m"][j] for j in range(21) if r["m"][j]}
        viol = None
        for k in range(3, 8):
            for S in itertools.combinations(range(7), k):
                nL, eL = line_graph_counts(m, set(S))
                if nL >= 3 and eL > 6 * nL - 12:
                    viol = (S, nL, eL)
                    break
            if viol:
                break
        if viol:
            hered_dead.append((r, viol))
            continue
        sub_tags = []
        for (u, v), x in m.items():
            if x == 7:
                S = [w for w in range(7) if w not in (u, v)]
                idx = {w: i for i, w in enumerate(S)}
                sub = {tuple(sorted((idx[a], idx[b]))): y for (a, b), y in m.items()
                       if a in idx and b in idx}
                sub_tags.append(names.get(canon5(sub), "??"))
        if any("LEAN" in t or "KSS" in t or "DEAD" in t for t in sub_tags):
            contained.append((r, sub_tags))
        else:
            alive.append((r, sub_tags))
    print(f"    killed by the hereditary edge bound: {len(hered_dead)}")
    for r, (S, nL, eL) in hered_dead:
        print(f"      e={r['e']}: S={S} gives L(M[S]) with n'={nL}, e'={eL} > {6 * nL - 12}")
    print(f"    killed by containing a dead 19-vertex line graph: {len(contained)}")
    for r, t in contained:
        print(f"      e={r['e']}: contains L-copy of {t}")
    tf_dead = []
    for r, t in list(alive):
        nL_, EL_ = line_graph({P7[j]: r["m"][j] for j in range(21) if r["m"][j]})
        if trifree_exceeds(nL_, EL_, 4 * nL_ - 8):
            tf_dead.append(r)
            alive.remove((r, t))
    print(f"    killed by the triangle-free count (> 4n-8 = 104): {len(tf_dead)}"
          f"{' (incl. C7xK4)' if any(r['is_4c7'] for r in tf_dead) else ''}")
    for r in tf_dead:
        print(f"      e={r['e']}{' (C7xK4)' if r['is_4c7'] else ''}")
    print(f"    OPEN: {len(alive)}")
    for r, t in sorted(alive, key=lambda z: z[0]["e"]):
        m = " ".join(f"{a}{b}:{r['m'][j]}" for j, (a, b) in enumerate(P7) if r["m"][j])
        extra = f"   <- decided by {t[0]}" if t else ""
        print(f"      e={r['e']} {'(C7xK4) ' if r['is_4c7'] else ''}{m}{extra}")


if __name__ == "__main__":
    main()
