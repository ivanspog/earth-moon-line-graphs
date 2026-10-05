#!/usr/bin/env python3
"""F-035: exact chi_f certificates and the cheap biplanarity counts for every window
member of families A and B (f035_circulant_family.py MEMBER lines).

For each member G = K_s v C_m(D) (vertices 0..n-1; asserted contiguous, no isolated
vertices, so no label-gap inflation of chi_f):

  chi_f   EXACT, two ways.
          (1) Closed-form rational certificates checked with fractions:
              dual  y = 1 on K_s, 1/alpha on H; every maximal independent set of G
                    (Bron-Kerbosch on the complement) has y-weight <= 1 => chi_f >= y(V);
              primal the s clique singletons at weight 1, plus the m rotations of one
                    maximum independent set of H at weight 1/alpha (each vertex of H
                    lies in exactly alpha rotations) => chi_f <= s + m/alpha.
          (2) f034_fractional_census.chi_f (LP over all maximal independent sets, then
              rounded primal and dual re-checked exactly): its certified lower bound must
              equal ours; its rounded primal may be looser than (1)'s, never tighter.
  counts  (a) hereditary Euler: max over S (|S| >= 3) of e(G[S]) - 6|S|, exact
              (RC2 MaxSAT); biplanar => <= -12.
          (b) hereditary triangle-free: max |T| - 4|S| over triangle-free T inside
              G[S], exact (f034_hereditary_trifree.best_margin); biplanar => <= -8.
              Tried first: an explicit witness (the edges between the cosets of a subgroup
              K with K \\ {0} inside D, checked triangle-free); if it already exceeds the bound
              the MaxSAT is skipped (it took > 20 min on C9 x K4, n = 36).
          (c) codegree: c1 + 2 c0 <= 4 * slack, where c_k = #edges whose endpoints have
              exactly k common neighbours and slack = 6n - 12 - e.  Proof: in a plane
              layer with n >= 3 vertices, e_i >= 2 edges and deficit d_i = 3n - 6 - e_i,
              Euler gives sum over faces of (len - 3) <= d_i, every face has len >= 3,
              so the non-triangular faces carry at most 4 d_i edge-sides.  A triangular
              face on edge uv has a common neighbour of u, v as its third vertex, and
              when e > 3n - 3 no layer is a lone triangle, so both sides of uv are
              triangular only if u, v have two common neighbours.  An edge with codegree
              0 thus puts 2 sides, one with codegree 1 at least 1 side, on non-triangular
              faces, and d_1 + d_2 = slack.  At slack 0 this is the F-034 A2 argument.

Run: .venv/bin/python -u verifier/f035_counts.py population/f035-family-A-M60.log
"""
import itertools
import os
import re
import sys
import time
from fractions import Fraction as Fr

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f034_fractional_census import chi_f as census_chi_f  # noqa: E402
from f034_hereditary_trifree import best_margin  # noqa: E402
from f035_circulant_family import (adj_bits, alpha_exact, conn_set,  # noqa: E402
                                   join_edges)


def hereditary_euler(n, E):
    """max over S, |S| >= 3, of e(G[S]) - 6|S|  (exact, RC2)."""
    E = [tuple(sorted(e)) for e in E]
    x = {e: i + 1 for i, e in enumerate(E)}
    y = {v: len(E) + 1 + v for v in range(n)}
    w = WCNF()
    for (u, v), xe in x.items():
        w.append([-xe, y[u]])
        w.append([-xe, y[v]])
    for cl in CardEnc.atleast(list(y.values()), 3, top_id=len(E) + n,
                              encoding=EncType.seqcounter).clauses:
        w.append(cl)
    for xe in x.values():
        w.append([xe], weight=1)
    for yv in y.values():
        w.append([-yv], weight=6)
    with RC2(w) as r:
        model = set(l for l in r.compute() if l > 0)
    S = {v for v in range(n) if y[v] in model}
    eS = sum(1 for u, v in E if u in S and v in S)  # re-count independently of x
    return eS - 6 * len(S), eS, len(S)


def coset_witness(s, m, D):
    """Explicit triangle-free witness, tried before the (slow at n >= 36) MaxSAT: for every
    subgroup K of Z_m with K \\ {0} inside D, take T = the edges of the circulant block whose
    difference is NOT in K (the edges between K-cosets).  T is checked triangle-free and
    counted exactly; S = the m circulant vertices.  Returns the best |T| - 4m, or None."""
    best = None
    for q in range(2, m + 1):
        if m % q:
            continue
        K = {(m // q) * i for i in range(q)}
        if not (K - {0}) <= set(D):
            continue
        T = [(s + v, s + (v + x) % m) for v in range(m) for x in D
             if x not in K and v < (v + x) % m]
        if T and sum(nx.triangles(nx.Graph(T)).values()) == 0:
            val = len(T) - 4 * m
            if best is None or val > best[0]:
                best = (val, len(T), m)
    return best


def codegree(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    c = [0, 0]
    for u, v in E:
        k = len(adj[u] & adj[v])
        if k < 2:
            c[k] += 1
    slack = 6 * n - 12 - len(E)
    return c[0], c[1], slack, c[1] + 2 * c[0] <= 4 * slack


def maximal_independent_sets(n, E):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(E)
    return [set(c) for c in nx.find_cliques(nx.complement(G))]


def certify(s, m, D, n, E):
    assert sorted({x for e in E for x in e}) == list(range(n)), "label gaps / isolated vertices"
    adj = adj_bits(m, D)
    a = alpha_exact(m, adj)
    # a maximum independent set of H containing 0 (vertex-transitive)
    Hg = nx.circulant_graph(m, sorted({min(x, m - x) for x in D}))
    I0 = max((c for c in nx.find_cliques(nx.complement(Hg)) if 0 in c), key=len)
    assert len(I0) == a
    y = {v: (Fr(1) if v < s else Fr(1, a)) for v in range(n)}
    mis = maximal_independent_sets(n, E)
    assert max(sum(y[v] for v in I) for I in mis) <= 1
    lo = sum(y.values())
    cover = {v: Fr(0) for v in range(n)}
    cols = [({v}, Fr(1)) for v in range(s)]
    cols += [({s + (u + r) % m for u in I0}, Fr(1, a)) for r in range(m)]
    Eset = set(E)
    for I, z in cols:
        assert all((min(p, q), max(p, q)) not in Eset for p, q in itertools.combinations(I, 2))
        for v in I:
            cover[v] += z
    assert all(cover[v] >= 1 for v in range(n))
    hi = sum(z for _, z in cols)
    assert lo == hi == s + Fr(m, a)
    # census: its dual must reproduce our value; its primal is only rounded at a few
    # fixed denominators, so it may be looser than our explicit primal (it is for C7xK4:
    # 1961/210), never tighter
    lo2, hi2, _, _ = census_chi_f(n, E)
    assert lo2 == lo and hi2 is not None and hi2 >= hi, (lo2, hi2, lo)
    return lo, len(mis), ("agrees" if hi2 == hi else f"lower agrees, its rounded primal {hi2} is looser")


def members(path):
    for line in open(path):
        if line.startswith("MEMBER"):
            f = line.rstrip("\n").split("\t")
            kv = dict(t.split("=", 1) for t in f[2:])
            yield f[1], int(kv["s"]), int(kv["m"]), tuple(int(x) for x in kv["S"].split(","))


if __name__ == "__main__":
    print(f"# f035_counts  pid {os.getpid()}  {time.ctime()}", flush=True)
    for tag, s, m, S in members(sys.argv[1]):
        D = conn_set(m, S)
        n, E = join_edges(s, m, D)
        name = f"K{s} v C{m}({','.join(map(str, S))})"
        t0 = time.time()
        cf, nmis, census = certify(s, m, D, n, E)
        he, heE, heS = hereditary_euler(n, E)
        wit = coset_witness(s, m, D)
        if wit is not None and wit[0] > -8:
            tf, tfT, tfS = wit  # explicit witness already kills; MaxSAT optimum not needed
            tfsrc = "explicit coset witness"
        else:
            tf, tfT, tfS = best_margin(n, E)
            tfsrc = "MaxSAT optimum"
        c0, c1, slack, cg_ok = codegree(n, E)
        dead = []
        if he > -12:
            dead.append(f"hereditary-Euler (S={heS}, e(S)={heE} > {6 * heS - 12})")
        if tf > -8:
            dead.append(f"triangle-free [{tfsrc}] (|S|={tfS}, |T|={tfT} > {4 * tfS - 8})")
        if not cg_ok:
            dead.append(f"codegree (c1+2c0={c1 + 2 * c0} > 4*slack={4 * slack})")
        verdict = "DEAD by " + "; ".join(dead) if dead else "SURVIVES all counts -> SAT"
        print(f"{tag}\t{name}\tn={n} e={len(E)} slack={slack}\tchi_f={cf} (certified, "
              f"{nmis} maximal IS; census LP {census})\theredEuler={he}\ttrifree={tf} [{tfsrc}] "
              f"(|T|={tfT},|S|={tfS})\tcodeg c0={c0} c1={c1}\t{verdict}  "
              f"[{time.time() - t0:.1f}s]", flush=True)
    print(f"# DONE {time.ctime()}", flush=True)
