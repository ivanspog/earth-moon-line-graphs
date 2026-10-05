#!/usr/bin/env python3
"""F-035 (milestone C-h6, step F1, family B): joins of two or more circulants,
G = K_s v H_1 v ... v H_r (r >= 2), the "H1 v H2" generalisation of family A.

Reduction to ESSENTIAL parts (each step replaces G by a subgraph with the same chi_f,
and a subgraph of a biplanar graph is biplanar, so nothing is lost):
  * a disconnected circulant is a disjoint union of isomorphic connected circulants;
    keep one component (chi_f of a disjoint union is the max over components);
  * a part with chi_f(H_i) = omega(H_i) is replaced by the clique K_{omega(H_i)} it
    contains and merged into K_s (chi_f of a join is additive).
So every part left is connected, non-complete, with chi_f(H_i) > omega(H_i) >= 2,
hence m_i >= 5.  With r <= 1 essential part the graph is in family A
(f035_circulant_family.py, P-007).  With r >= 2: K_{m_i, m_j} is a triangle-free
subgraph, so biplanarity needs m_i m_j <= 4(m_i + m_j) - 8, i.e. (m_i-4)(m_j-4) <= 8,
which forces every m_i <= 12 (a part with m >= 13 against one with m' >= 5 gives
(m-4)(m'-4) >= 9).  The universe is therefore finite and enumerated completely here:
all multisets of r = 2..4 essential circulants on 5..12 vertices (omega(G) <= 8 and
omega_i >= 2 force r <= 4) and every s = 0..8.

Filters in order (first kill counted): omega(G) <= 8; the pairwise K_{m_i,m_j}
count; e(G) <= 6n - 12; window chi_f(G) >= 9.  Window members print as MEMBER lines.

Run: .venv/bin/python -u verifier/f035_circulant_joins.py
"""
import itertools
import os
import sys
from fractions import Fraction as Fr
from math import comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from f035_circulant_family import adj_bits, alpha_exact, circulants, omega_vt  # noqa: E402


def essential(mlo=5, mhi=12):
    out = []
    for m in range(mlo, mhi + 1):
        for S, D in circulants(m):
            adj = adj_bits(m, D)
            a, w = alpha_exact(m, adj), omega_vt(m, adj)
            cf = Fr(m, a)
            if cf > w:
                out.append(dict(m=m, S=S, D=D, d=len(D), alpha=a, omega=w, chi_f=cf))
    return out


def multi_join_edges(s, parts):
    """K_s on 0..s-1, then each circulant part on a consecutive block; all cross edges."""
    blocks, off = [], s
    for p in parts:
        blocks.append(range(off, off + p["m"]))
        off += p["m"]
    n = off
    E = set(itertools.combinations(range(s), 2))
    everything = list(range(n))
    owner = {}
    for i, b in enumerate(blocks):
        for v in b:
            owner[v] = i
    for u, v in itertools.combinations(everything, 2):
        if u < s or owner[u] != owner[v]:
            E.add((u, v))
    for p, b in zip(parts, blocks):
        m = p["m"]
        for v in range(m):
            for x in p["D"]:
                u = (v + x) % m
                if v < u:
                    E.add((b[v], b[u]))
    return n, sorted(E)


def main():
    ess = essential()
    print(f"# {len(ess)} essential circulants (connected, non-complete, chi_f > omega) on 5..12 vertices:")
    for p in ess:
        print(f"#   C_{p['m']}({','.join(map(str, p['S']))}) d={p['d']} alpha={p['alpha']} "
              f"omega={p['omega']} chi_f={p['chi_f']}")
    kills = {"omega": 0, "Kmm": 0, "euler": 0, "window": 0}
    members = []
    total = 0
    for r in (2, 3, 4):
        for parts in itertools.combinations_with_replacement(range(len(ess)), r):
            P = [ess[i] for i in parts]
            for s in range(0, 9):
                total += 1
                if s + sum(p["omega"] for p in P) > 8:
                    kills["omega"] += 1
                    continue
                if any((a["m"] - 4) * (b["m"] - 4) > 8 for a, b in itertools.combinations(P, 2)):
                    kills["Kmm"] += 1
                    continue
                n = s + sum(p["m"] for p in P)
                e = (comb(s, 2) + s * (n - s) + sum(p["d"] * p["m"] // 2 for p in P)
                     + sum(a["m"] * b["m"] for a, b in itertools.combinations(P, 2)))
                if e > 6 * n - 12:
                    kills["euler"] += 1
                    continue
                cf = s + sum(p["chi_f"] for p in P)
                if cf < 9:
                    kills["window"] += 1
                    continue
                nn, E = multi_join_edges(s, P)
                assert nn == n and len(E) == e
                members.append((cf, s, P, n, e))
    print(f"# family B: {total} (s, multiset) configurations with r = 2..4 essential parts")
    print(f"# killed: omega>8 {kills['omega']}, (m_i-4)(m_j-4)>8 {kills['Kmm']}, "
          f"e>6n-12 {kills['euler']}, chi_f<9 {kills['window']}; window: {len(members)}")
    assert sum(kills.values()) + len(members) == total
    for cf, s, P, n, e in members:
        tag = "TARGET" if cf > 9 else "BOUNDARY"
        desc = " v ".join(f"C_{p['m']}({','.join(map(str, p['S']))})" for p in P)
        print(f"MEMBER\t{tag}\tK{s} v {desc}\tn={n}\te={e}\tslack={6 * n - 12 - e}\tchi_f={cf}")


if __name__ == "__main__":
    main()
