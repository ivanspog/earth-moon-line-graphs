"""SAT attack on biplanarity with a LAZY PLANARITY PROPAGATOR (IPASIR-UP,
KSS-style but in pure Python via pysat + CaDiCaL 1.9.5).

Same base encoding as biplanar_sat.py (edge -> part variables, cardinality
<= 3n-6 per part, preseeded K5/K3,3 split clauses, lex symmetry breaking
over automorphism generators, part-swap unit). On top of it, a propagator
observes the edge variables and, on partial assignments, checks planarity
of each part; when a part goes non-planar it hands the solver the
falsified Kuratowski clause immediately, pruning the subtree — instead of
waiting for a full model as plain CEGAR does.

Soundness: every external clause is a Kuratowski split clause (implied by
biplanarity); complete models are additionally re-checked in check_model
(both parts planar via networkx) before SAT is accepted.

Usage:
  .venv/bin/python verifier/biplanar_sat_prop.py --weights 3,4,4,4,4
  .venv/bin/python verifier/biplanar_sat_prop.py --json suite/sulanke.json
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
from pysat.engines import Propagator
from pysat.formula import IDPool
from pysat.solvers import Cadical195

sys.path.insert(0, os.path.dirname(__file__))
from biplanar_sat import (inflation_automorphisms, k33_subgraphs,  # noqa: E402
                          k5_subgraphs, lex_leq)
from c5_inflation_attack import inflate_c5  # noqa: E402
from clause_dump import ClauseDump  # noqa: E402
from kuratowski_cert import (clique_certificate, extract_certificate,  # noqa: E402
                             k33_certificate)

ROOT = os.path.join(os.path.dirname(__file__), "..")

# Planarity backend for the propagator (F-034 A3: networkx's Kuratowski
# extraction was 87 % of runtime).  "boyer" = Boyer's edge-addition C library
# (PyPI `planarity`, ~470x faster on test + extraction, agreement 2000/2000 and
# every certificate valid in the 2026-09-24 check).  Every emitted clause is
# still validated by is_kuratowski_subdivision, and a SAT partition is still
# re-verified with networkx in solve(), so the trust story is unchanged.
# Override with BIPLANAR_PLANARITY=networkx.
try:
    import planarity as _boyer
except ImportError:  # pragma: no cover
    _boyer = None
BACKEND = os.environ.get("BIPLANAR_PLANARITY",
                         "boyer" if _boyer is not None else "networkx")


def planar_or_kuratowski(edge_list, n=None):
    """(True, None) if planar, else (False, sorted Kuratowski-subdivision edges)."""
    if BACKEND == "boyer":
        if _boyer.is_planar(edge_list):
            return True, None
        return False, [tuple(sorted(e)) for e in _boyer.kuratowski_edges(edge_list)]
    g = nx.Graph(edge_list)
    if n is not None:
        g.add_nodes_from(range(n))
    ok, cert = nx.check_planarity(g, counterexample=True)
    return (True, None) if ok else (False, [tuple(sorted(e)) for e in cert.edges()])


def is_kuratowski_subdivision(kedges):
    """NetworkX-independent validity check for an emitted certificate
    (added after adversarial review of P-005): smooth all degree-2 vertices and
    verify the result is literally K5 or K3,3. If so, the edge set
    contains a Kuratowski subdivision and is non-planar by the elementary
    direction of Kuratowski's theorem — so the split clause 'these edges
    cannot all be in one part' IS implied by biplanarity, independent of
    networkx's planarity verdict. Any failure only ever REJECTS (the
    caller raises), never accepts a wrong certificate."""
    adjm = {}
    for u, v in kedges:
        if u == v:
            return False
        adjm.setdefault(u, set()).add(v)
        adjm.setdefault(v, set()).add(u)
    changed = True
    while changed:
        changed = False
        for v in list(adjm):
            if v in adjm and len(adjm[v]) == 2:
                a, b = adjm[v]
                if a == b or b in adjm[a]:
                    return False  # loop or parallel edge: not a subdivision
                adjm[a].discard(v)
                adjm[b].discard(v)
                adjm[a].add(b)
                adjm[b].add(a)
                del adjm[v]
                changed = True
    if len(adjm) == 5:
        return all(len(s) == 4 for s in adjm.values())  # simple => K5
    if len(adjm) == 6 and all(len(s) == 3 for s in adjm.values()):
        vs = list(adjm)
        side_b = adjm[vs[0]]
        side_a = set(vs) - side_b
        if len(side_a) != 3 or len(side_b) != 3:
            return False
        return all(adjm[a] == side_b for a in side_a) and \
            all(adjm[b] == side_a for b in side_b)  # excludes the prism
    return False


class PlanarityProp(Propagator):
    """Tracks the two edge parts along the trail; emits Kuratowski clauses."""

    def __init__(self, n, edges, check_at=9, dump=None):
        super().__init__()
        self.is_lazy = False
        self.n, self.edges, self.m = n, edges, len(edges)
        self.check_at = check_at        # only test planarity above this size
        self.dump = dump                # optional ClauseDump (Lean milestone P1)
        self.trail = []                 # list of lists (per level) of lits
        self.level0 = []                # fixed assignments
        self.assign = {}                # var -> bool (edge in part2)
        self.queue = []                 # external clauses to hand over
        self.dirty = [False, False]
        self.stats = {"checks": 0, "confl": 0, "model_rej": 0}
        self.t0 = time.time()

    # -- trail bookkeeping -------------------------------------------------
    def on_assignment(self, lit, fixed=False):
        v = abs(lit)
        if v > self.m or v in self.assign:
            return
        self.assign[v] = lit > 0
        self.dirty[1 if lit > 0 else 0] = True
        (self.level0 if fixed or not self.trail else self.trail[-1]).append(v)

    def on_new_level(self):
        self.trail.append([])

    def on_backtrack(self, to):
        while len(self.trail) > to:
            for v in self.trail.pop():
                self.assign.pop(v, None)

    # -- planarity reasoning ----------------------------------------------
    def _part_edges(self, part2):
        return [self.edges[v - 1] for v, val in self.assign.items()
                if val == part2]

    def _check_part(self, part2):
        pe = self._part_edges(part2)
        if len(pe) <= self.check_at:
            return None
        self.stats["checks"] += 1
        if self.stats["checks"] % 50000 == 0:
            print(f"    ... {self.stats} {time.time() - self.t0:.0f}s",
                  flush=True)
        ok, kedges = planar_or_kuratowski(pe)
        if ok:
            return None
        assert is_kuratowski_subdivision(kedges), \
            f"INVALID CERTIFICATE from {BACKEND}: {kedges}"
        eidx = {e: i + 1 for i, e in enumerate(self.edges)}
        sign = -1 if part2 else 1
        # falsified now: every K-edge must leave this part
        clause = [sign * eidx[e] for e in kedges]
        # mirrored clause for the other part (valid, not falsified)
        mirror = [-l for l in clause]
        if self.dump is not None:
            kc = extract_certificate(kedges)
            self.dump.emit("prop", 1 if part2 else 0, kedges, kc)
            self.dump.emit("prop", 0 if part2 else 1, kedges, kc)
        return clause, mirror

    def propagate(self):
        for p in (0, 1):
            if self.dirty[p]:
                self.dirty[p] = False
                res = self._check_part(bool(p))
                if res:
                    self.stats["confl"] += 1
                    self.queue.extend(res)
                    break
        return []

    def provide_reason(self, lit):  # we never propagate literals directly
        return []

    def has_clause(self):
        if not self.queue:
            self.propagate()
        return bool(self.queue)

    def add_clause(self):
        return self.queue.pop(0) if self.queue else []

    def check_model(self, model):
        parts = ([], [])
        for l in model:
            v = abs(l)
            if 1 <= v <= self.m:
                parts[1 if l > 0 else 0].append(self.edges[v - 1])
        for p in (0, 1):
            ok, kedges = planar_or_kuratowski(parts[p], self.n)
            if not ok:
                assert is_kuratowski_subdivision(kedges), \
                    f"INVALID CERTIFICATE from {BACKEND}: {kedges}"
                eidx = {e: i + 1 for i, e in enumerate(self.edges)}
                sign = -1 if p else 1
                self.queue.append([sign * eidx[e] for e in kedges])
                if self.dump is not None:
                    self.dump.emit("model", p, kedges, extract_certificate(kedges))
                self.stats["model_rej"] += 1
                return False
        return True


def solve(n, edges, name, autos=None, check_at=9, extra_units=None,
          dump_path=None):
    """extra_units: optional iterable of edge-variable unit literals
    (±(edge_index+1)) appended as unit clauses — used by the cube-and-
    conquer audit driver (biplanar_sat_cube.py). Default None: encoding
    unchanged.
    dump_path: optional JSONL path (Lean milestone P1, additive): every
    pre-seed and every propagator/model Kuratowski clause is written with
    an explicit subdivision certificate (clause_dump.py). Default None:
    behaviour unchanged."""
    edges = [tuple(sorted(e)) for e in edges]
    m = len(edges)
    eidx = {e: i for i, e in enumerate(edges)}
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    cap = 3 * n - 6
    pool = IDPool(start_from=m + 1)
    x = list(range(1, m + 1))

    solver = Cadical195()
    ncl = 0

    def add(cl):
        nonlocal ncl
        solver.add_clause(cl)
        ncl += 1

    # automorphism generators -> induced edge-index permutations, computed
    # BEFORE the dump header so the header can record exactly the generators
    # whose lex clauses are added below (a generator that does not preserve
    # the edge set is dropped from both).
    gens = []
    for p in (autos or []):
        try:
            ep = [eidx[tuple(sorted((p[u], p[v])))] for u, v in edges]
        except KeyError:
            continue  # not an automorphism of this edge set; skip defensively
        gens.append(([p[v] for v in range(n)], ep))
    eperms = [ep for _, ep in gens]

    dump = None
    if dump_path:
        dump = ClauseDump(dump_path, n, edges, cap, name,
                          sym_on=bool(autos), extra_units=extra_units,
                          check_at=check_at,
                          script=os.path.basename(__file__), gens=gens)

    add([-x[0]])
    for lit in (extra_units or []):
        add([lit])
    for cnf in (CardEnc.atmost(lits=x, bound=cap, vpool=pool,
                               encoding=EncType.seqcounter),
                CardEnc.atleast(lits=x, bound=max(0, m - cap), vpool=pool,
                                encoding=EncType.seqcounter)):
        for cl in cnf.clauses:
            add(cl)

    def split(edge_list, cert=None):
        lits = [x[eidx[e]] for e in edge_list]
        add(lits)
        add([-l for l in lits])
        if dump is not None:
            dump.emit("preseed", 0, edge_list, cert)
            dump.emit("preseed", 1, edge_list, cert)

    k5s = k5_subgraphs(n, adj)
    for c in k5s:
        split(list(itertools.combinations(sorted(c), 2)),
              clique_certificate(c) if dump else None)
    k33s = k33_subgraphs(n, adj)
    for a, b in k33s:
        split([tuple(sorted((u, v))) for u in a for v in b],
              k33_certificate(a, b) if dump else None)

    for gi, ep in enumerate(eperms):
        ncl += lex_leq(solver, pool, x, [x[ep[i]] for i in range(m)],
                       ("lex", gi))

    prop = PlanarityProp(n, edges, check_at=check_at, dump=dump)
    solver.connect_propagator(prop)
    for v in x:
        solver.observe(v)

    print(f"[{name}] n={n} m={m} cap={cap} | {len(k5s)} K5s, {len(k33s)} "
          f"K3,3s, {len(eperms)} sym generators, {ncl} clauses, "
          f"propagator check_at={check_at} planarity={BACKEND}"
          + (f", clause dump -> {dump_path}" if dump else ""), flush=True)

    t0 = time.time()
    res = solver.solve()
    dt = time.time() - t0
    print(f"[{name}] stats: {prop.stats}", flush=True)
    if dump is not None:
        dump.close("UNSAT" if not res else "SAT", prop.stats)
        print(f"[{name}] clause dump closed: {dump.count}", flush=True)
    if not res:
        print(f"[{name}] UNSAT in {dt:.1f}s — NOT BIPLANAR "
              f"(subject to control validation)", flush=True)
        return "UNSAT", dt
    model = set(l for l in solver.get_model() if abs(l) <= m)
    p2 = [edges[i] for i in range(m) if (i + 1) in model]
    p1 = [edges[i] for i in range(m) if -(i + 1) in model]
    # final independent verification
    for tag, part in (("E1", p1), ("E2", p2)):
        g = nx.Graph(part)
        g.add_nodes_from(range(n))
        assert nx.check_planarity(g)[0], f"{tag} NON-PLANAR — bug"
    assert len(p1) + len(p2) == m and not set(p1) & set(p2)
    out = os.path.join(ROOT, "population", f"satprop_{name}_partition.json")
    with open(out, "w") as f:
        json.dump({"num_vertices": n, "edges_part1": [list(e) for e in p1],
                   "edges_part2": [list(e) for e in p2],
                   "method": "biplanar_sat_prop IPASIR-UP"}, f)
    print(f"[{name}] SAT in {dt:.1f}s — BIPLANAR PARTITION FOUND -> {out}",
          flush=True)
    return "SAT", dt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights")
    ap.add_argument("--json")
    ap.add_argument("--check-at", type=int, default=9)
    ap.add_argument("--no-sym", action="store_true",
                    help="disable automorphism lex symmetry breaking (for "
                         "over-pruning audits; slower but fewer hand-written "
                         "constraints)")
    ap.add_argument("--dump-clauses", metavar="PATH",
                    help="write every pre-seed / propagator Kuratowski clause "
                         "with its subdivision certificate to a JSONL file "
                         "(Lean verification feed; sym-on runs are liftable "
                         "too since the header records the generators)")
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
    if args.no_sym:
        autos, name = None, name + "_nosym"
    solve(n, edges, name, autos=autos, check_at=args.check_at,
          dump_path=args.dump_clauses)


if __name__ == "__main__":
    main()
