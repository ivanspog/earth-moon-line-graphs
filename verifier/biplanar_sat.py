"""Definitive SAT attack on biplanarity of a FIXED graph.

Encoding: one Boolean x_e per edge (False = part1, True = part2).
  - part-swap symmetry broken by fixing edge 0 into part1;
  - cardinality: each part has at most 3n-6 edges (planar bound);
  - pre-seeded non-planarity clauses: every K5 subgraph and every K3,3
    subgraph must be split (sound: a part containing one is non-planar);
  - lazy Kuratowski CEGAR: on a SAT model, check both parts planar with
    networkx; a non-planar part yields a Kuratowski subgraph K, and we add
    BOTH clauses "not all of K in part1" / "not all of K in part2"
    (roles are symmetric). Several K's are extracted per counterexample by
    edge deletion. Learned K's are persisted to a jsonl side file so an
    interrupted run can re-seed.

Soundness of UNSAT: every clause is implied by biplanarity (monochromatic
non-planar subgraph = contradiction; cardinality is Euler's bound), and
SAT models are accepted only after a direct networkx planarity check of
both parts. Mandatory controls before trusting any UNSAT on the unknowns:
this encoding must FIND the known partition of Sulanke's C5 v K6 (SAT)
and must reproduce KSS 2023's non-biplanarity of C5[3,4,4,4,4] (UNSAT).

Usage:
  .venv/bin/python verifier/biplanar_sat.py --weights 3,4,4,4,4
  .venv/bin/python verifier/biplanar_sat.py --json suite/sulanke.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
import time

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

sys.path.insert(0, os.path.dirname(__file__))
from c5_inflation_attack import inflate_c5  # noqa: E402

ROOT = os.path.join(os.path.dirname(__file__), "..")


def k5_subgraphs(n, adj):
    """All 5-cliques, as frozensets of vertices."""
    out = []
    for clq in nx.find_cliques(nx.Graph([(u, v) for u in range(n)
                                         for v in adj[u] if u < v])):
        if len(clq) >= 5:
            out += [frozenset(c) for c in itertools.combinations(sorted(clq), 5)]
    return sorted(set(out), key=sorted)


def k33_subgraphs(n, adj):
    """All K3,3 subgraphs: unordered pairs of disjoint triples (A,B) with all
    nine cross edges present. Returned as (tuple(A), tuple(B))."""
    out = set()
    verts = list(range(n))
    for b in itertools.combinations(verts, 3):
        common = adj[b[0]] & adj[b[1]] & adj[b[2]]
        common -= set(b)
        cs = sorted(common)
        for a in itertools.combinations(cs, 3):
            key = tuple(sorted((tuple(sorted(a)), tuple(sorted(b)))))
            out.add(key)
    return sorted(out)


def inflation_automorphisms(w):
    """Generators of Aut(C5[w]) as vertex permutations (dicts):
    within-bag adjacent transpositions + dihedral symmetries of C5 that
    preserve the weight vector."""
    L = len(w)
    bags, s = [], 0
    for x in w:
        bags.append(list(range(s, s + x)))
        s += x
    gens = []
    for b in bags:
        for i in range(len(b) - 1):
            p = {v: v for v in range(sum(w))}
            p[b[i]], p[b[i + 1]] = b[i + 1], b[i]
            gens.append(p)
    # dihedral maps i -> (d*i + t) mod L preserving weights, bag j -> bag image
    for t in range(L):
        for d in (1, -1):
            if (t, d) == (0, 1):
                continue
            img = [(d * i + t) % L for i in range(L)]
            if all(w[img[i]] == w[i] for i in range(L)):
                p = {}
                for i in range(L):
                    for a, v in enumerate(bags[i]):
                        p[v] = bags[img[i]][a]
                gens.append(p)
    return gens


def lex_leq(solver, pool, xs, ys, tag):
    """Clauses for xs <=_lex ys. Activity chain a_i = 'prefix 0..i-1 equal':
    a_0 = true; a_i -> (x_i <= y_i); a_i & (x_i = y_i) -> a_{i+1}.
    Sound for satisfiability: the lex-min solution of any orbit extends the
    a_i by their exact semantics and satisfies every clause."""
    n = len(xs)
    a = [pool.id((tag, i)) for i in range(n)]
    cls = [[a[0]]]
    for i in range(n):
        cls.append([-a[i], -xs[i], ys[i]])
        if i + 1 < n:
            cls.append([-a[i], xs[i], ys[i], a[i + 1]])
            cls.append([-a[i], -xs[i], -ys[i], a[i + 1]])
    for c in cls:
        solver.add_clause(c)
    return len(cls)


def kuratowski_edge_sets(part_edges, n, tries=8):
    """Extract up to `tries` distinct Kuratowski subgraphs (as edge tuples)
    from a non-planar part, by deleting one edge of each found K and
    re-checking. Returns [] if the part is planar."""
    g = nx.Graph(part_edges)
    g.add_nodes_from(range(n))
    found = []
    ok, cert = nx.check_planarity(g, counterexample=True)
    if ok:
        return []
    seen = set()
    stack = [g]
    while stack and len(found) < tries:
        h = stack.pop()
        ok, cert = nx.check_planarity(h, counterexample=True)
        if ok:
            continue
        kedges = frozenset(tuple(sorted(e)) for e in cert.edges())
        if kedges in seen:
            continue
        seen.add(kedges)
        found.append(sorted(kedges))
        # branch: delete each of a few edges of this K to look for others
        for e in list(kedges)[:3]:
            h2 = h.copy()
            h2.remove_edge(*e)
            stack.append(h2)
    return found


def solve(n, edges, name, learned_path=None, log_every=25, autos=None):
    edges = [tuple(sorted(e)) for e in edges]
    m = len(edges)
    eidx = {e: i for i, e in enumerate(edges)}
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    cap = 3 * n - 6
    pool = IDPool(start_from=m + 1)
    x = list(range(1, m + 1))  # x[i] true => edge i in part2

    def split_clauses(edge_list):
        """Clauses forcing the given edge set not to be monochromatic."""
        lits = [x[eidx[e]] for e in edge_list]
        return [lits, [-l for l in lits]]

    solver = Cadical195()
    nclauses = 0

    def add(cl):
        nonlocal nclauses
        solver.add_clause(cl)
        nclauses += 1

    add([-x[0]])  # symmetry: edge 0 in part1 (lex vs part-swap)

    # automorphism machinery: vertex perms -> edge-index perms
    eperms = []
    for p in (autos or []):
        try:
            eperms.append([eidx[tuple(sorted((p[u], p[v])))] for u, v in edges])
        except KeyError:
            pass  # not an automorphism of this edge set; skip defensively

    def orbit_closure(kedges_list, cap=400):
        """Close a list of edge sets under the generators (each image of a
        Kuratowski subgraph is one). Returns list of edge-index frozensets."""
        seen, queue = set(), []
        for ke in kedges_list:
            fs = frozenset(eidx[tuple(sorted(e))] for e in ke)
            if fs not in seen:
                seen.add(fs)
                queue.append(fs)
        qi = 0
        while qi < len(queue) and len(seen) < cap:
            fs = queue[qi]
            qi += 1
            for ep in eperms:
                img = frozenset(ep[i] for i in fs)
                if img not in seen:
                    seen.add(img)
                    queue.append(img)
        return list(seen)
    # cardinality: |part2| <= cap  and  |part1| <= cap i.e. |part2| >= m-cap
    for cnf in (CardEnc.atmost(lits=x, bound=cap, vpool=pool,
                               encoding=EncType.seqcounter),
                CardEnc.atleast(lits=x, bound=max(0, m - cap), vpool=pool,
                                encoding=EncType.seqcounter)):
        for cl in cnf.clauses:
            add(cl)

    def split_clauses_idx(idxs):
        lits = [x[i] for i in idxs]
        return [lits, [-l for l in lits]]

    nlex = 0
    for gi, ep in enumerate(eperms):
        nlex += lex_leq(solver, pool, x, [x[ep[i]] for i in range(m)],
                        ("lex", gi))
    nclauses += nlex
    if eperms:
        print(f"[{name}] symmetry: {len(eperms)} automorphism generators, "
              f"{nlex} lex clauses", flush=True)

    k5s = k5_subgraphs(n, adj)
    for c in k5s:
        for cl in split_clauses(list(itertools.combinations(sorted(c), 2))):
            add(cl)
    k33s = k33_subgraphs(n, adj)
    for a, b in k33s:
        cross = [tuple(sorted((u, v))) for u in a for v in b]
        for cl in split_clauses(cross):
            add(cl)
    print(f"[{name}] n={n} m={m} cap={cap} | preseed: {len(k5s)} K5s, "
          f"{len(k33s)} K3,3s, {nclauses} clauses", flush=True)

    # re-seed previously learned Kuratowski subgraphs (orbit-closed)
    if learned_path and os.path.exists(learned_path):
        raw = []
        for line in open(learned_path):
            kedges = [tuple(sorted(e)) for e in json.loads(line)]
            if all(e in eidx for e in kedges):
                raw.append(kedges)
        n_add = 0
        for fs in orbit_closure(raw, cap=min(120000, max(4000, 3 * len(raw)))):
            for cl in split_clauses_idx(fs):
                add(cl)
            n_add += 1
        print(f"[{name}] re-seeded {len(raw)} learned Kuratowski subgraphs "
              f"-> {n_add} after orbit closure", flush=True)

    t0 = time.time()
    it = 0
    while True:
        it += 1
        if not solver.solve():
            dt = time.time() - t0
            print(f"[{name}] UNSAT after {it} iterations, {nclauses} clauses, "
                  f"{dt:.1f}s — NOT BIPLANAR (subject to control validation)",
                  flush=True)
            return ("UNSAT", it, dt)
        model = set(l for l in solver.get_model() if 0 < l <= m)
        p2 = [edges[i] for i in range(m) if (i + 1) in model]
        p1 = [edges[i] for i in range(m) if (i + 1) not in model]
        new = 0
        fresh = []
        for part in (p1, p2):
            for kedges in kuratowski_edge_sets(part, n):
                fresh.append(kedges)
                if learned_path:
                    with open(learned_path, "a") as f:
                        f.write(json.dumps([list(e) for e in kedges]) + "\n")
        if fresh:
            for fs in orbit_closure(fresh, cap=60 * len(fresh)):
                for cl in split_clauses_idx(fs):
                    add(cl)
                new += 1
        if new == 0:
            dt = time.time() - t0
            out = os.path.join(ROOT, "population", f"sat_{name}_partition.json")
            with open(out, "w") as f:
                json.dump({"num_vertices": n,
                           "edges_part1": [list(e) for e in p1],
                           "edges_part2": [list(e) for e in p2],
                           "method": "biplanar_sat CEGAR"}, f)
            print(f"[{name}] SAT after {it} iterations, {dt:.1f}s — "
                  f"BIPLANAR PARTITION FOUND -> {out}", flush=True)
            return ("SAT", it, dt)
        if it % log_every == 0:
            print(f"[{name}] iter {it}: {nclauses} clauses, "
                  f"{time.time() - t0:.0f}s", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", help="C5 inflation weights, e.g. 3,4,4,4,4")
    ap.add_argument("--json", help="graph json with num_vertices + edges_part*")
    args = ap.parse_args()
    autos = None
    if args.weights:
        w = [int(t) for t in args.weights.split(",")]
        n, edges = inflate_c5(w)
        name = "c5_" + "_".join(map(str, w))
        autos = inflation_automorphisms(w)
    else:
        obj = json.load(open(args.json))
        n = obj["num_vertices"]
        edges = [tuple(sorted(e)) for e in
                 obj.get("edges_part1", []) + obj.get("edges_part2", [])]
        name = os.path.splitext(os.path.basename(args.json))[0]
    learned = os.path.join(ROOT, "population", f"sat_{name}_learned.jsonl")
    solve(n, edges, name, learned_path=learned, autos=autos)


if __name__ == "__main__":
    main()
