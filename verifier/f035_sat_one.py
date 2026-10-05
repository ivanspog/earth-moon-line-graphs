#!/usr/bin/env python3
"""F-035: biplanarity SAT (Boyer backend, lazy Kuratowski propagator) for one member
G = K_s v C_m(D) of the circulant-join family, with symmetry breaking.

Usage: f035_sat_one.py s m S1,S2,...  [--no-sym]
Prints 'RESULT <name> SAT|UNSAT <sec>'.  A SAT partition is written by solve() to
population/satprop_<name>_partition.json after solve()'s own networkx re-check; this
script then re-verifies it with networkx AND Boyer independently (disjoint, union = E,
both parts planar).

Symmetry generators (lex-leader, one constraint per generator; sound for any subset
of the automorphism group, and compatible with solve()'s part-swap unit because swap
commutes with every vertex permutation):
  * adjacent transpositions inside every closed-twin class of G (N[u] = N[v]); this
    covers S_s on the clique and the K_2 blow-ups (C_5 x K_2, C_8^2 x K_2);
  * on the circulant block: rotation v -> v+1, reflection v -> -v, and every
    multiplier u (unit mod m, u != +-1) with uD = D.
Every generator is asserted to be an automorphism before it is passed on (solve()
would otherwise drop a non-automorphism silently).
"""
import json
import os
import sys
import time

import networkx as nx
import planarity

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from biplanar_sat_prop import solve  # noqa: E402
from f035_circulant_family import conn_set, join_edges, units  # noqa: E402


def generators(s, m, D, n, E):
    Eset = set(E)
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    gens = []

    def perm_from(f):
        p = list(range(n))
        for v in range(m):
            p[s + v] = s + f(v) % m
        return p

    # closed-twin classes
    closed = {}
    for v in range(n):
        closed.setdefault(frozenset(adj[v] | {v}), []).append(v)
    for cls in closed.values():
        for a, b in zip(cls, cls[1:]):
            p = list(range(n))
            p[a], p[b] = b, a
            gens.append(p)
    gens.append(perm_from(lambda v: v + 1))
    gens.append(perm_from(lambda v: -v))
    Dset = set(D)
    for u in units(m):
        if u in (1, m - 1):
            continue
        if {u * x % m for x in D} == Dset:
            gens.append(perm_from(lambda v, u=u: u * v))
    for p in gens:
        assert sorted(p) == list(range(n))
        assert all((min(p[a], p[b]), max(p[a], p[b])) in Eset for a, b in E), "not an automorphism"
    return gens


def reverify(path, n, E):
    obj = json.load(open(path))
    p1 = [tuple(sorted(e)) for e in obj["edges_part1"]]
    p2 = [tuple(sorted(e)) for e in obj["edges_part2"]]
    assert obj["num_vertices"] == n
    assert not set(p1) & set(p2) and set(p1) | set(p2) == set(E) and len(p1) + len(p2) == len(E)
    for part in (p1, p2):
        g = nx.Graph()
        g.add_nodes_from(range(n))
        g.add_edges_from(part)
        assert nx.check_planarity(g)[0], "networkx: part not planar"
        assert planarity.is_planar(part), "Boyer: part not planar"
    return len(p1), len(p2)


def main():
    s, m = int(sys.argv[1]), int(sys.argv[2])
    S = [int(x) for x in sys.argv[3].split(",")]
    sym = "--no-sym" not in sys.argv
    D = conn_set(m, S)
    n, E = join_edges(s, m, D)
    name = f"f035-K{s}vC{m}({'.'.join(map(str, S))})" + ("" if sym else "_nosym")
    autos = generators(s, m, D, n, E) if sym else None
    print(f"[{name}] n={n} e={len(E)} generators={len(autos) if autos else 0}", flush=True)
    t = time.time()
    res, _ = solve(n, E, name, autos=autos, check_at=9)
    if res == "SAT":
        path = os.path.join(HERE, "..", "population", f"satprop_{name}_partition.json")
        a, b = reverify(path, n, E)
        print(f"[{name}] partition re-verified: networkx AND Boyer planar, |E1|={a} |E2|={b}",
              flush=True)
    print(f"RESULT {name} {res} {time.time() - t:.1f}s", flush=True)


if __name__ == "__main__":
    main()
