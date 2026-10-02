"""F-032 step 1: enumerate the 8-regular loopless multigraphs on 7 vertices
whose line graphs could be a biplanar chi>=10 example.

Constraints derived in findings/F-032-line-graph-route.md:
  * 7 vertices, every degree exactly 8  (so |E(M)| = 28 = |V(L(M))|)
  * every triple multiplicity sum m_ij+m_ik+m_jk <= 8   (omega(L(M)) <= 8;
    the maximal cliques of a line graph are stars and triangles)
  * e(L(M)) = 196 - sum_{i<j} C(m_ij,2) must be <= 6*28-12 = 156,
    i.e. sum_{i<j} C(m_ij,2) >= 40 -- the binding constraint, used to prune
  * chi(L(M)) = chi'(M) >= 10, tested by SAT (L(M) not 9-colourable)

Usage: .venv/bin/python -u verifier/f032_enumerate.py
"""
from __future__ import annotations

import itertools
import sys
import time

N, DEG, TOTAL = 7, 8, 28
TRI_CAP = 8
MIN_F = 40

PAIRS = [(i, j) for i in range(N) for j in range(i + 1, N)]
NP = len(PAIRS)
PIDX = {p: k for k, p in enumerate(PAIRS)}
PAIR_AT = [[None] * N for _ in range(N)]
for k, (i, j) in enumerate(PAIRS):
    PAIR_AT[i][j] = PAIR_AT[j][i] = k

TRIPLES = list(itertools.combinations(range(N), 3))
TRI_PAIRS = [(PIDX[(a, b)], PIDX[(a, c)], PIDX[(b, c)]) for (a, b, c) in TRIPLES]
TRI_OF = [[] for _ in range(NP)]          # triple ids containing this pair
for t, ids in enumerate(TRI_PAIRS):
    for k in ids:
        TRI_OF[k].append(t)

ROW_DONE = [[] for _ in range(NP)]        # rows finalised once this pair is set
for i in range(N - 1):
    ROW_DONE[PIDX[(i, N - 1)]].append(i)
ROW_DONE[PIDX[(N - 2, N - 1)]].append(N - 1)
CHECKPOINTS = {p for p in range(NP) if ROW_DONE[p]}

F = [m * (m - 1) // 2 for m in range(DEG + 1)]


def enumerate_labeled(log_every=20_000_000):
    m = [0] * NP
    deg = [0] * N
    tri = [0] * len(TRIPLES)
    out = []
    nodes = [0]
    t0 = time.time()

    def cap_of(p, i, j):
        c = min(DEG - deg[i], DEG - deg[j])
        for t in TRI_OF[p]:
            c = min(c, TRI_CAP - tri[t])
        return c

    def prune(p):
        """Degree feasibility + an upper bound on the achievable sum C(m,2)."""
        extra = 0
        for i in range(N):
            r = DEG - deg[i]
            if r == 0:
                continue
            caps = []
            tot = 0
            for j in range(N):
                if j == i:
                    continue
                q = PAIR_AT[i][j]
                if q <= p:
                    continue
                c = cap_of(q, i, j)
                if c:
                    caps.append(c)
                    tot += c
            if tot < r:                    # cannot reach degree 8
                return True
            caps.sort(reverse=True)
            left, best = r, 0
            for c in caps:
                take = c if c < left else left
                best += F[take]
                left -= take
                if not left:
                    break
            extra += best
        return fs[0] + extra / 2 < MIN_F

    fs = [0]

    def rec(p, msum):
        nodes[0] += 1
        if nodes[0] % log_every == 0:
            print(f"  ... {nodes[0]:,} nodes, {len(out):,} solutions, "
                  f"{time.time() - t0:.0f}s", flush=True)
        if p == NP:
            if msum == TOTAL and fs[0] >= MIN_F:
                out.append(tuple(m))
            return
        i, j = PAIRS[p]
        hi = min(cap_of(p, i, j), TOTAL - msum)
        for v in range(hi, -1, -1):
            m[p] = v
            deg[i] += v
            deg[j] += v
            for t in TRI_OF[p]:
                tri[t] += v
            fs[0] += F[v]
            ok = all(deg[r] == DEG for r in ROW_DONE[p])
            if ok and p in CHECKPOINTS and p < NP - 1:
                ok = not prune(p)
            if ok:
                rec(p + 1, msum + v)
            fs[0] -= F[v]
            deg[i] -= v
            deg[j] -= v
            for t in TRI_OF[p]:
                tri[t] -= v
        m[p] = 0

    rec(0, 0)
    print(f"  search: {nodes[0]:,} nodes in {time.time() - t0:.1f}s", flush=True)
    return out


PERMS = [tuple(PAIR_AT[pm[a]][pm[b]] for (a, b) in PAIRS)
         for pm in itertools.permutations(range(N))]


def invariant(v):
    rows = tuple(sorted(tuple(sorted(v[PAIR_AT[i][j]] for j in range(N) if j != i))
                        for i in range(N)))
    tri = tuple(sorted(v[a] + v[b] + v[c] for (a, b, c) in TRI_PAIRS))
    return (rows, tri, tuple(sorted(v)))


def classes(labeled):
    buckets = {}
    for v in labeled:
        buckets.setdefault(invariant(v), []).append(v)
    reps = []
    for members in buckets.values():
        pool = set(members)
        while pool:
            v = min(pool)
            orbit = {tuple(v[q[k]] for k in range(NP)) for q in PERMS}
            reps.append(min(orbit))
            pool -= orbit
    return sorted(reps)


def line_graph(v):
    edges = []
    for k, (i, j) in enumerate(PAIRS):
        edges.extend([(i, j)] * v[k])
    n = len(edges)
    E = [(a, b) for a in range(n) for b in range(a + 1, n)
         if set(edges[a]) & set(edges[b])]
    return n, E, edges


def greedy9(n, adj, order):
    col = [-1] * n
    for u in order:
        used = {col[w] for w in adj[u] if col[w] >= 0}
        for c in range(9):
            if c not in used:
                col[u] = c
                break
        else:
            return None
    return col


def chi_ge_10(n, E, edges):
    """True iff L(M) is NOT 9-colourable, i.e. chi'(M) >= 10."""
    adj = [[] for _ in range(n)]
    for (a, b) in E:
        adj[a].append(b)
        adj[b].append(a)
    # cheap positive answer first: a 9-colouring found by greedy settles it
    for start in range(min(n, 8)):
        order = sorted(range(n), key=lambda u: (-len(adj[u]), (u - start) % n))
        if greedy9(n, adj, order) is not None:
            return False
    from pysat.solvers import Cadical195
    K = 9
    s = Cadical195()
    for u in range(n):
        s.add_clause([u * K + c + 1 for c in range(K)])
    for (a, b) in E:
        for c in range(K):
            s.add_clause([-(a * K + c + 1), -(b * K + c + 1)])
    # symmetry breaking: the 8 edges of M at vertex 0 are a K8 in L(M);
    # pin them to colours 0..7 (any 9-colouring can be permuted to this)
    star = [k for k in range(n) if 0 in edges[k]]
    for c, u in enumerate(star[:8]):
        s.add_clause([u * K + c + 1])
    r = s.solve()
    s.delete()
    return not r


def main():
    print("enumerating labeled solutions ...", flush=True)
    labeled = enumerate_labeled()
    print(f"labeled solutions: {len(labeled):,}", flush=True)
    reps = classes(labeled)
    print(f"isomorphism classes: {len(reps)}\n", flush=True)
    import json
    json.dump([list(v) for v in reps], open("verifier/f032_classes.json", "w"))
    survivors = []
    for v in reps:
        n, E, edges = line_graph(v)
        fsum = sum(F[x] for x in v)
        mult = {f"{i}-{j}": v[k] for k, (i, j) in enumerate(PAIRS) if v[k]}
        print(f"  L(M): n={n} e={len(E)}  sumC(m,2)={fsum}  m = {mult}", flush=True)
        big = chi_ge_10(n, E, edges)
        print(f"      chi>=10: {big}", flush=True)
        if big:
            survivors.append(v)
    print(f"\nSURVIVORS (biplanar-feasible AND chi>=10): {len(survivors)} "
          f"of {len(reps)} classes")
    for v in survivors:
        print("  ", {f"{i}-{j}": v[k] for k, (i, j) in enumerate(PAIRS) if v[k]})


if __name__ == "__main__":
    main()
