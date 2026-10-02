#!/usr/bin/env python3
"""F-037 (F5 own attempt): shared exact helpers.

chi_f by LP over all maximal independent sets (scipy/HiGHS), then EXACT rational
certificates both ways (dual: every maximal IS has weight <= 1; primal: every vertex
covered >= 1).  Vertices must be 0..n-1 (relabel first).  Small graphs only.
"""
from __future__ import annotations
import math
from fractions import Fraction as Fr

import networkx as nx
import numpy as np
from scipy.optimize import linprog


def mis_list(G):
    """All maximal independent sets of G (as sorted lists)."""
    return [sorted(c) for c in nx.find_cliques(nx.complement(G))]


def _exact_primal(S, n, x):
    """Exact rational primal on the HiGHS support: solve A[tight,J] z = 1 by Fraction
    Gauss-Jordan (picking independent tight rows); returns z (list) or None."""
    J = [j for j, v in enumerate(x) if v > 1e-9]
    cover = [sum(x[j] for j in J if v in S[j]) for v in range(n)]
    rows = [v for v in range(n) if abs(cover[v] - 1) < 1e-7]
    M = [[Fr(1 if v in S[j] else 0) for j in J] + [Fr(1)] for v in rows]
    piv, r = [], 0
    for c in range(len(J)):
        pr = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = 1 / M[r][c]
        M[r] = [a * inv for a in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    if len(piv) < len(J) or any(all(a == 0 for a in row[:-1]) and row[-1] != 0 for row in M):
        return None
    z = [Fr(0)] * len(S)
    for i, c in enumerate(piv):
        z[J[c]] = M[i][-1]
    if any(v < 0 for v in z):
        return None
    if all(sum(z[j] for j in J if v in S[j]) >= 1 for v in range(n)):
        return z
    return None


def chi_f(G, exact=True):
    """Return (lo, hi, dual_weights) with lo <= chi_f <= hi certified exactly.
    If exact=False return (float, float, float-dual)."""
    n = G.number_of_nodes()
    assert sorted(G.nodes()) == list(range(n))
    S = mis_list(G)
    A = np.zeros((n, len(S)))
    for j, s in enumerate(S):
        A[s, j] = 1
    d = linprog(-np.ones(n), A_ub=A.T, b_ub=np.ones(len(S)), bounds=(0, None), method="highs")
    if not exact:
        return -d.fun, -d.fun, d.x
    p = linprog(np.ones(len(S)), A_ub=-A, b_ub=-np.ones(n), bounds=(0, None), method="highs")
    lo = hi = None
    yl = None
    for D in (2, 6, 12, 24, 60, 120, 360, 840, 2520, 27720):
        y = [Fr(round(v * D), D) for v in d.x]
        if all(sum(y[v] for v in s) <= 1 for s in S):
            if lo is None or sum(y) > lo:
                lo, yl = sum(y), y
            if abs(float(lo) + d.fun) < 1e-9:
                break
    z = _exact_primal(S, n, p.x)
    if z is not None:
        hi = sum(z)
    for D in (2, 6, 12, 24, 60, 120, 360, 840, 2520, 27720):
        if hi is not None and lo is not None and hi == lo:
            break
        z = [Fr(math.ceil(v * D - 1e-9), D) if v > 1e-12 else Fr(0) for v in p.x]
        if all(sum(z[j] for j, s in enumerate(S) if v in s) >= 1 for v in range(n)):
            if hi is None or sum(z) < hi:
                hi = sum(z)
            if abs(float(hi) - p.fun) < 1e-9:
                break
    return lo, hi, yl


def degeneracy(G):
    """max over the smallest-last order of the back-degree (= max core number)."""
    return max(nx.core_number(G).values()) if G.number_of_nodes() else 0


def omega(G):
    return max((len(c) for c in nx.find_cliques(G)), default=0)


def relabel(G):
    return nx.convert_node_labels_to_integers(G)
