"""F-032 step 2: filter the 73 enumerated classes and test chi >= 10.

Reads verifier/f032_classes.json (written by f032_enumerate.py).

Filters, in order of cost:
  * Euler bound PER CONNECTED COMPONENT: a biplanar component with n_c >= 3
    vertices has at most 6 n_c - 12 edges.  (The global count is not enough:
    an 8-fold edge contributes a cheap K8 component that masks an overfull
    one elsewhere.)
  * chi(L(M)) = chi'(M) >= 10, by SAT, with the K8 star clique pinned.
"""
from __future__ import annotations

import itertools
import json
import sys

N = 7
PAIRS = [(i, j) for i in range(N) for j in range(i + 1, N)]


def line_graph(v):
    edges = []
    for k, (i, j) in enumerate(PAIRS):
        edges.extend([(i, j)] * v[k])
    n = len(edges)
    adj = [set() for _ in range(n)]
    for a in range(n):
        for b in range(a + 1, n):
            if set(edges[a]) & set(edges[b]):
                adj[a].add(b)
                adj[b].add(a)
    return n, adj, edges


def components(n, adj):
    seen, comps = [False] * n, []
    for s in range(n):
        if seen[s]:
            continue
        stack, comp = [s], []
        seen[s] = True
        while stack:
            u = stack.pop()
            comp.append(u)
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = True
                    stack.append(w)
        comps.append(comp)
    return comps


def euler_ok(n, adj):
    """Every component with >= 3 vertices satisfies e <= 6n - 12."""
    for comp in components(n, adj):
        nc = len(comp)
        if nc < 3:
            continue
        cs = set(comp)
        ec = sum(len(adj[u] & cs) for u in comp) // 2
        if ec > 6 * nc - 12:
            return False, (nc, ec, 6 * nc - 12)
    return True, None


def chi_ge_10(n, adj, edges):
    from pysat.solvers import Cadical195
    K = 9
    s = Cadical195()
    for u in range(n):
        s.add_clause([u * K + c + 1 for c in range(K)])
    for u in range(n):
        for w in adj[u]:
            if w > u:
                for c in range(K):
                    s.add_clause([-(u * K + c + 1), -(w * K + c + 1)])
    star = [k for k in range(n) if 0 in edges[k]]
    for c, u in enumerate(star[:8]):
        s.add_clause([u * K + c + 1])
    r = s.solve()
    s.delete()
    return not r


def mults(v):
    return {f"{i}-{j}": v[k] for k, (i, j) in enumerate(PAIRS) if v[k]}


def is_4c7(v):
    """4*C7: seven pairs of multiplicity 4 forming a 7-cycle."""
    if sorted(x for x in v if x) != [4] * 7:
        return False
    deg = {}
    for k, (i, j) in enumerate(PAIRS):
        if v[k]:
            deg.setdefault(i, []).append(j)
            deg.setdefault(j, []).append(i)
    return len(deg) == 7 and all(len(a) == 2 for a in deg.values())


def _job(v):
    n, adj, edges = line_graph(v)
    e = sum(len(a) for a in adj) // 2
    return (v, n, e, len(components(n, adj)), chi_ge_10(n, adj, edges))


def main():
    reps = [tuple(x) for x in json.load(open("verifier/f032_classes.json"))]
    print(f"classes from the enumeration: {len(reps)}\n")
    stage = []
    for v in reps:
        n, adj, edges = line_graph(v)
        ok, why = euler_ok(n, adj)
        ncomp = len(components(n, adj))
        stage.append((v, n, adj, edges, ok, why, ncomp))
    passed = [s for s in stage if s[4]]
    print(f"pass the per-component Euler bound: {len(passed)} of {len(reps)}")
    killed = [s for s in stage if not s[4]]
    print(f"  killed by a component with e > 6n-12: {len(killed)}")
    conn = [s for s in passed if s[6] == 1]
    print(f"  of the survivors, connected: {len(conn)}\n")
    from concurrent.futures import ProcessPoolExecutor
    survivors, results = [], []
    with ProcessPoolExecutor(max_workers=6) as ex:
        for (v, n, e, ncomp, big) in ex.map(_job, [s[0] for s in passed]):
            tag = "  <-- C7 (strong) K4 = L(4*C7)" if is_4c7(v) else ""
            print(f"  n={n} e={e} comps={ncomp} chi>=10: {big}{tag}")
            print(f"     m = {mults(v)}", flush=True)
            results.append({"m": list(v), "n": n, "e": e, "comps": ncomp,
                            "chi_ge_10": big, "is_4c7": is_4c7(v)})
            if big:
                survivors.append((v, n, e, ncomp))
    json.dump(results, open("verifier/f032_results.json", "w"), indent=1)
    print(f"\n=== SURVIVORS (component-Euler AND chi>=10): {len(survivors)} ===")
    for (v, n, e, ncomp) in survivors:
        tag = "   [= C7 (strong product) K4, our C-h1 target]" if is_4c7(v) else ""
        print(f"  n={n} e={e} components={ncomp}  m = {mults(v)}{tag}")


if __name__ == "__main__":
    main()
