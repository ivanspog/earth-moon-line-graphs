#!/usr/bin/env python3
"""F-035 (milestone C-h6, step F1, family A): joins of a clique with a circulant,
G = K_s v C_m(D).  Pure computation: no Brooks / Reed / Kneser is used here, so this
script is an independent check of the all-m theorem P-007 inside its range.

Universe.  Every connected, non-complete circulant H = C_m(D) (D = -D, 0 not in D),
3 <= m <= M, up to multiplier equivalence (D ~ uD, u a unit mod m; isomorphic
duplicates are possible for non-CI orders, which only over-counts), and every
s = 0..8.  For m >= 18 only degrees <= 11 are enumerated: for m >= 18 every degree
>= 12 violates e(G) <= 6n - 12 for every s (e(G) - 6n + 12 = C(s,2) + sm + dm/2 - 6s
- 6m + 12, and the degree bound 12 - 2s + (13s - s^2 - 24)/m is < 12 for s = 0 and
<= 11 for s >= 1, m >= 18), so those pairs are Euler-dead without enumeration.

Filters, in order, each (s, H) pair counted once at the first filter that kills it:
  omega   omega(G) = s + omega(H) <= 8        (K9 is not biplanar)
  euler   e(G) <= 6n - 12
  window  chi_f(G) = s + m/alpha(H) >= 9      (chi_f of a vertex-transitive graph is
                                               m/alpha; chi_f of a join is additive)
Window members are split into TARGET (chi_f > 9) and BOUNDARY (chi_f = 9) and printed
as MEMBER lines; the hereditary counts and SAT act on those (f035_counts.py,
f035_sat_one.py).

alpha is decided exactly by a bitset branch-and-bound with vertex 0 forced into the
set (vertex-transitivity), and re-checked with networkx on every window member.

Run: .venv/bin/python -u verifier/f035_circulant_family.py [M]   (default M = 50)
"""
import itertools
import sys
import time
from fractions import Fraction as Fr
from math import comb, gcd

import networkx as nx


def units(m):
    return [u for u in range(1, m) if gcd(u, m) == 1]


def canon(m, S, U):
    """Lexicographically least short-representative form of S under multipliers."""
    return min(tuple(sorted(min(u * x % m, m - u * x % m) for x in S)) for u in U)


def conn_set(m, S):
    """D = +-S as a set of residues."""
    return sorted({x % m for x in S} | {(-x) % m for x in S})


def adj_bits(m, D):
    adj = []
    for v in range(m):
        b = 0
        for x in D:
            b |= 1 << ((v + x) % m)
        adj.append(b)
    return adj


def has_is(adj, cand, need):
    """Is there an independent set of size `need` inside bitmask `cand`?"""
    if need <= 0:
        return True
    while cand:
        if cand.bit_count() < need:
            return False
        v = (cand & -cand).bit_length() - 1
        cand &= ~(1 << v)
        if has_is(adj, cand & ~adj[v], need - 1):
            return True
    return False


def alpha_at_least(m, adj, k):
    """alpha(C_m(D)) >= k ?  (vertex 0 WLOG in the set: vertex-transitive)."""
    if k <= 1:
        return True
    full = (1 << m) - 1
    return has_is(adj, full & ~adj[0] & ~1, k - 1)


def alpha_exact(m, adj):
    k = 1
    while alpha_at_least(m, adj, k + 1):
        k += 1
    return k


def omega_vt(m, adj):
    best = 1

    def rec(cand, size):
        nonlocal best
        best = max(best, size)
        while cand:
            if size + cand.bit_count() <= best:
                return
            v = (cand & -cand).bit_length() - 1
            cand &= ~(1 << v)
            rec(cand & adj[v], size + 1)

    rec(adj[0], 1)
    return best


def circulants(m):
    """Connected non-complete circulants on m vertices, one per multiplier class.
    Yields (S, D) with S the canonical short form."""
    U = units(m)
    half = m // 2 if m % 2 == 0 else None
    pool = list(range(1, (m - 1) // 2 + 1))
    kmax = len(pool) if m < 18 else 5
    for k in range(0, kmax + 1):
        for T in itertools.combinations(pool, k):
            for with_half in ((False, True) if half else (False,)):
                S = T + ((half,) if with_half else ())
                if not S:
                    continue
                if m >= 18 and 2 * k + with_half > 11:
                    continue
                if canon(m, S, U) != tuple(sorted(S)):
                    continue
                g = m
                for x in S:
                    g = gcd(g, x)
                if g != 1:
                    continue  # disconnected: a disjoint union of copies of a smaller circulant
                D = conn_set(m, S)
                if len(D) == m - 1:
                    continue  # complete: G = K_{s+m}, chi_f = omega <= 8
                yield tuple(sorted(S)), D


def join_edges(s, m, D):
    """K_s on 0..s-1, C_m(D) on s..s+m-1, all s*m join edges.  Vertices are 0..n-1."""
    E = set(itertools.combinations(range(s), 2))
    E |= {(a, s + v) for a in range(s) for v in range(m)}
    for v in range(m):
        for x in D:
            u = (v + x) % m
            if v < u:
                E.add((s + v, s + u))
    return s + m, sorted(E)


def main(M):
    t0 = time.time()
    kills = {"omega": 0, "euler": 0, "window": 0}
    target, boundary = [], []
    n_H = 0
    per_m = []
    for m in range(3, M + 1):
        cnt = 0
        for S, D in circulants(m):
            cnt += 1
            n_H += 1
            d = len(D)
            adj = adj_bits(m, D)
            w = omega_vt(m, adj)
            passing = []
            for s in range(0, 9):
                if s + w > 8:
                    kills["omega"] += 1
                    continue
                n = s + m
                e = comb(s, 2) + s * m + d * m // 2
                if e > 6 * n - 12:
                    kills["euler"] += 1
                    continue
                passing.append(s)
            if not passing:
                continue
            # window: s + m/alpha >= 9  <=>  alpha <= m/(9-s); largest s is the easiest
            s1 = max(passing)
            kmax = m // (9 - s1)  # alpha must be <= kmax for the easiest s
            if alpha_at_least(m, adj, kmax + 1):
                kills["window"] += len(passing)
                continue
            a = alpha_exact(m, adj)
            for s in passing:
                cf = s + Fr(m, a)
                if cf < 9:
                    kills["window"] += 1
                    continue
                n, E = join_edges(s, m, D)
                # independent re-check of alpha and omega with networkx
                Hg = nx.circulant_graph(m, [x for x in S])
                a_nx = max(len(c) for c in nx.find_cliques(nx.complement(Hg)))
                w_nx = max(len(c) for c in nx.find_cliques(Hg))
                assert (a_nx, w_nx) == (a, w), (m, S, a, a_nx, w, w_nx)
                row = dict(s=s, m=m, S=S, d=d, n=n, e=len(E), slack=6 * n - 12 - len(E),
                           alpha=a, omega=s + w, chi_f=cf)
                (target if cf > 9 else boundary).append(row)
        per_m.append((m, cnt))
        print(f"m={m}: {cnt} circulant classes  [{time.time() - t0:.0f}s]", flush=True)
    pairs = 9 * n_H
    print(f"# family A: K_s v C_m(D), 0 <= s <= 8, 3 <= m <= {M}: {n_H} circulant classes, "
          f"{pairs} (s, H) pairs")
    print(f"# killed: omega>8 {kills['omega']}, e>6n-12 {kills['euler']}, "
          f"chi_f<9 {kills['window']}; window: {len(target)} with chi_f>9, "
          f"{len(boundary)} with chi_f=9")
    assert kills["omega"] + kills["euler"] + kills["window"] + len(target) + len(boundary) == pairs
    for tag, rows in (("TARGET", target), ("BOUNDARY", boundary)):
        for r in rows:
            print(f"MEMBER\t{tag}\ts={r['s']}\tm={r['m']}\tS={','.join(map(str, r['S']))}\t"
                  f"d={r['d']}\tn={r['n']}\te={r['e']}\tslack={r['slack']}\t"
                  f"alpha(H)={r['alpha']}\tomega(G)={r['omega']}\tchi_f={r['chi_f']}", flush=True)
    print(f"# DONE {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 50)
