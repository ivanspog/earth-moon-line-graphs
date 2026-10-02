#!/usr/bin/env python3
"""F-034 step A4: sym-on biplanarity SAT for one open line graph L(M) (F-032/F-033).

Usage:  f034_a4_line_graph_sat.py --list          # print "index slack e mults" for the open set
        f034_a4_line_graph_sat.py <index>         # run the solver on that member
        f034_a4_line_graph_sat.py <index> --dump PATH   # same run, plus a clause dump
        f034_a4_line_graph_sat.py <index> --dump PATH --cube L1 L2 …   # one cube only

The open set is recomputed from verifier/f033_line_graph_route.py (23 members) minus
the one killed by A1 (f034_hereditary_trifree: e=156 `05:2 06:6 14:4 15:3 16:1 23:4
25:3 26:1 34:4`) -> 22.  Symmetry generators, each asserted here to be a bijection
of V(L(M)) preserving E(L(M)) before use:
  * adjacent transpositions of the parallel copies of every multi-edge of M;
  * every non-identity automorphism of M (vertex permutations of the 7 vertices
    preserving all multiplicities), acting copy-for-copy.
Backend: whatever biplanar_sat_prop.BACKEND is (boyer by default).  No clause dump
by default (disk); an UNSAT is a deterministic run and can be replayed with
--dump PATH for Lean: the same solve() call with dump_path set, so the search is
unchanged (the dump only records the clauses it emits, each with a subdivision
certificate, and the header records the generators, which is what lets the
sym-on refutation lift via LEAN-2).  The replay must reproduce the original
run's final `stats:` line exactly; verifier/f034_a4_certify.sh checks that.
"""
import itertools
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

P7 = list(itertools.combinations(range(7), 2))
KILLED_A1 = "05:2 06:6 14:4 15:3 16:1 23:4 25:3 26:1 34:4"


CACHE = os.path.join(HERE, "..", "population", "f034-a4", "open_members.json")


def _mults_dict(mults):
    return {(int(t[0]), int(t[1])): int(t.split(":")[1]) for t in mults.split()}


def open_members():
    """The 22 open members, recomputed from f033_line_graph_route.py (~30 s) or
    read from the cache that the first computation writes (F-038 §10: the
    per-cube search starts one solver per cube, so the enumeration would
    otherwise run hundreds of times). The cache holds (slack, e, mults) only;
    `--recompute` ignores it and checks that the enumeration still agrees."""
    if os.path.exists(CACHE) and "--recompute" not in sys.argv:
        return [(sl, e, mu, _mults_dict(mu)) for sl, e, mu in json.load(open(CACHE))]
    out = subprocess.run([sys.executable, os.path.join(HERE, "f033_line_graph_route.py")],
                         capture_output=True, text=True, check=True).stdout
    rows = []
    for row in out.split("OPEN:")[1].strip().split("\n")[1:]:
        toks = row.split()
        mults = " ".join(t for t in toks[1:] if ":" in t)
        if mults == KILLED_A1:
            continue
        e = int(toks[0].split("=")[1])
        rows.append((6 * 28 - 12 - e, e, mults, _mults_dict(mults)))
    rows.sort(key=lambda r: (r[0], r[2]))
    flat = [[sl, e, mu] for sl, e, mu, _ in rows]
    if os.path.exists(CACHE):
        assert json.load(open(CACHE)) == flat, "open_members.json disagrees with the enumeration"
    else:
        json.dump(flat, open(CACHE, "w"))
    return rows


def build(m):
    lab = []  # vertex of L(M) -> (edge of M, copy index)
    for (a, b), k in sorted(m.items()):
        for c in range(k):
            lab.append(((a, b), c))
    idx = {x: i for i, x in enumerate(lab)}
    n = len(lab)
    E = sorted((i, j) for i, j in itertools.combinations(range(n), 2)
               if set(lab[i][0]) & set(lab[j][0]))
    Eset = set(E)
    gens = []

    def check_and_add(p):
        assert sorted(p) == list(range(n)), "not a bijection"
        assert {tuple(sorted((p[u], p[v]))) for u, v in E} == Eset, "not an automorphism"
        gens.append({v: p[v] for v in range(n)})

    for (a, b), k in sorted(m.items()):
        for c in range(k - 1):
            p = list(range(n))
            i, j = idx[((a, b), c)], idx[((a, b), c + 1)]
            p[i], p[j] = j, i
            check_and_add(p)
    for pi in itertools.permutations(range(7)):
        if pi == tuple(range(7)):
            continue
        if all(m.get(tuple(sorted((pi[a], pi[b]))), 0) == k for (a, b), k in m.items()):
            p = [idx[(tuple(sorted((pi[e[0]], pi[e[1]]))), c)] for e, c in lab]
            check_and_add(p)
    return n, E, gens


def main():
    rows = open_members()
    if sys.argv[1] == "--list":
        for i, (slack, e, mults, _) in enumerate(rows):
            print(i, slack, e, mults)
        return
    i = int(sys.argv[1])
    dump = sys.argv[sys.argv.index("--dump") + 1] if "--dump" in sys.argv else None
    cube = []   # --cube L1 L2 …: DIMACS unit literals on edge variables (one cube of a split)
    if "--cube" in sys.argv:
        for t in sys.argv[sys.argv.index("--cube") + 1:]:
            if t.startswith("--"):
                break
            cube.append(int(t))
    slack, e, mults, m = rows[i]
    n, E, gens = build(m)
    assert all(0 < abs(l) <= len(E) for l in cube), "cube literals must be edge variables"
    from biplanar_sat_prop import BACKEND, solve
    name = f"f034-a4-{i:02d}-e{e}"
    print(f"# A4 member {i}: slack={slack} e={e} n={n} mults=[{mults}] "
          f"generators={len(gens)} backend={BACKEND} {time.ctime()}"
          + (f" cube={cube}" if cube else ""), flush=True)
    t0 = time.time()
    res = solve(n, E, name, autos=gens, check_at=9, dump_path=dump,
                extra_units=cube or None)
    print(f"RESULT {name} {res[0]} {time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
