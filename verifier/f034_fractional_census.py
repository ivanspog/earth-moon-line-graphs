#!/usr/bin/env python3
"""F-034 step B1: fractional census of known biplanar graphs.

For every whole graph in a directory of edge lists (default: Patil's MIT-licensed
corpus, github.com/Volkopat/earth-moon-biplanar data/graphs, 241 files incl. layers),
compute chi_f exactly:

  * LP over all maximal independent sets (scipy / HiGHS) gives a candidate value;
  * the LP dual is rounded to rationals and CHECKED EXACTLY (every maximal
    independent set has weight <= 1), which proves chi_f >= total;
  * the LP primal is rounded and checked exactly (every vertex covered >= 1),
    which proves chi_f <= total.  Both bounds must agree for the value to be reported
    as exact; otherwise the certified interval is printed.

Biplanarity: where `<name>_layer*.edges` files exist, each layer is tested planar
(networkx) and their union is checked to equal the graph.  Graphs without layers
are reported as UNVERIFIED-biplanar (the corpus asserts it; we do not).

Run: .venv/bin/python verifier/f034_fractional_census.py <corpus-dir>
"""
import glob
import math
import os
import re
import sys
from fractions import Fraction as Fr

import networkx as nx
import numpy as np
from scipy.optimize import linprog


def load(path):
    E = set()
    for line in open(path):
        t = line.split()
        if len(t) >= 2 and t[0].lstrip("-").isdigit():
            u, v = int(t[0]), int(t[1])
            if u != v:
                E.add((min(u, v), max(u, v)))
    return E


def maximal_independent_sets(n, adj):
    # maximal cliques of the complement
    G = nx.Graph()
    G.add_nodes_from(range(n))  # isolated vertices must be in G BEFORE complementing
    G.add_edges_from((u, v) for u in range(n) for v in adj[u])
    comp = nx.complement(G)
    return [sorted(c) for c in nx.find_cliques(comp)]


def chi_f(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    S = maximal_independent_sets(n, adj)
    A = np.zeros((n, len(S)))
    for j, s in enumerate(S):
        A[s, j] = 1
    d = linprog(-np.ones(n), A_ub=A.T, b_ub=np.ones(len(S)), bounds=(0, None), method="highs")
    p = linprog(np.ones(len(S)), A_ub=-A, b_ub=-np.ones(n), bounds=(0, None), method="highs")
    # exact certificates
    lo = None
    for D in (6, 12, 24, 60, 120, 360, 840, 2520):
        y = [Fr(round(v * D), D) for v in d.x]
        if all(sum(y[v] for v in s) <= 1 for s in S):
            lo = sum(y)
            if abs(float(lo) + d.fun) < 1e-9:
                break
    hi = None
    for D in (6, 12, 24, 60, 120, 360, 840, 2520):
        z = [Fr(math.ceil(v * D - 1e-9), D) if v > 1e-12 else Fr(0) for v in p.x]
        if all(sum(z[j] for j, s in enumerate(S) if v in s) >= 1 for v in range(n)):
            hi = sum(z)
            if abs(float(hi) - p.fun) < 1e-9:
                break
    alpha = max(len(s) for s in S)
    return lo, hi, alpha, len(S)


def main(corpus):
    files = sorted(glob.glob(os.path.join(corpus, "**", "*.edges"), recursive=True))
    whole = [f for f in files if not re.search(r"_layer\d*\.edges$", f)]
    rows = []
    for f in whole:
        E = load(f)
        E0 = set(E)
        V = sorted({x for e in E for x in e})
        relabel = {v: i for i, v in enumerate(V)}  # drop label gaps (isolated vertices)
        E = {(relabel[u], relabel[v]) for u, v in E}
        n = len(V)
        base = f[:-len(".edges")]
        layers = sorted(glob.glob(base + "_layer*.edges"))
        if layers:
            L = [load(x) for x in layers]
            ok = all(nx.check_planarity(nx.Graph(list(l)))[0] for l in L) and set().union(*L) == E0
            bip = "layers-verified" if ok else "LAYERS-FAIL"
        else:
            bip = "unverified"
        lo, hi, alpha, nS = chi_f(n, E)
        omega = max(len(c) for c in nx.find_cliques(nx.Graph(list(E))))
        rows.append((lo if lo is not None else Fr(0), hi, os.path.relpath(f, corpus), n, len(E), alpha, omega, bip))
    rows.sort(key=lambda r: -r[0])
    print(f"# fractional census of {len(rows)} whole graphs in {corpus}")
    print("# chi_f (certified lower = upper unless shown) | file | n e alpha omega | biplanarity")
    for lo, hi, f, n, e, a, w, b in rows:
        val = f"{lo}" if hi == lo else f"[{lo}, {hi}]"
        print(f"{float(lo):7.4f}  {val:>9}  {f:45s} n={n:<3} e={e:<4} alpha={a} omega={w}  {b}")


if __name__ == "__main__":
    main(sys.argv[1])
