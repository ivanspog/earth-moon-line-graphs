"""Differential check: Lean's lex block == pysat's lex_leq clause set.

Soundness of the lex clauses is proved in `lean/Biplanar/Sym.lean`, and the
Lean-exported formula is what CaDiCaL refutes, so a mismatch here could never
make a theorem wrong — but it would make the exported formula satisfiable and
waste a multi-hour solver run. This compares, for an instance whose dump
recorded automorphism generators:

  * the lex clauses of `lean/data/<key>/F.cnf` (written by
    `lake exe biplanar-export`, so exactly `Biplanar.lexAll`), against
  * the clauses `lex_leq` (verifier/biplanar_sat.py) produces for the same
    generators — the ones the solver search actually ran with,

after renaming each activity variable to its (block, position) pair. The two
must agree except for the tautological clauses at generator-fixed positions,
which Lean must omit (its LRAT checker drops tautologies and renumbers).

Usage:
  .venv/bin/python verifier/lex_encoding_diff.py --key k9sym \
      --graph population/lean-pilot/k9sym-core/graph.json
"""
from __future__ import annotations

import argparse
import json
import os
import sys

from pysat.formula import IDPool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from biplanar_sat import lex_leq  # noqa: E402

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


class _Collect:
    def __init__(self):
        self.out = []

    def add_clause(self, cl):
        self.out.append(list(cl))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--key", required=True)
    ap.add_argument("--graph", required=True, help="graph.json with `gens`")
    ap.add_argument("--cnf", default=None, help="default lean/data/<key>/F.cnf")
    ap.add_argument("--skip", type=int, default=0,
                    help="leading clauses to skip (the cube units of a leaf CNF "
                         "written by `biplanar-export <key> <out> <cube lits>`)")
    ap.add_argument("--counters", action="store_true",
                    help="the formula is mkCNFSym (the lex block starts after "
                         "both counter blocks) rather than mkCNFSym₀")
    args = ap.parse_args()

    g = json.load(open(args.graph))
    m, gens = len(g["edges"]), g["gens"]
    assert gens, "graph.json records no generators"
    cnf_path = args.cnf or os.path.join(ROOT, "lean", "data", args.key, "F.cnf")
    cls = [[int(t) for t in line.split()[:-1]]
           for line in open(cnf_path) if not line.startswith("p")][args.skip:]

    # mkCNFSym₀: part-swap unit, then the lex blocks (activities from m).
    # mkCNFSym: part-swap unit, two Sinz counters `atMostSeq` of
    # k + (m-1)(2k+1) clauses each (Biplanar/Basic.lean), then the lex blocks
    # with activities from `actBase` = m + 2mk (Biplanar/SymDefs.lean).
    k = g["cap"]
    base = m + 2 * m * k if args.counters else m
    nunit = 1 + 2 * (k + (m - 1) * (2 * k + 1)) if args.counters else 1
    assert cls[nunit] == [base + 1], \
        f"lex block does not start at clause {nunit} (found {cls[nunit]})"
    nfixed = sum(1 for gg in gens for i in range(m) if gg["eperm"][i] == i)
    nlex = len(gens) * (1 + m + 2 * (m - 1)) - nfixed
    lean_lex = cls[nunit:nunit + nlex]

    def canon_lean(lit):
        v = abs(lit) - 1
        if v < base:
            return (lit > 0, "x", v)
        d = v - base
        return (lit > 0, "a", d // m, d % m)

    pool = IDPool(start_from=m + 1)
    x = list(range(1, m + 1))
    col, aux = _Collect(), {}
    for t, gg in enumerate(gens):
        ep = gg["eperm"]
        lex_leq(col, pool, x, [x[ep[i]] for i in range(m)], ("lex", t))
        for i in range(m):
            aux[pool.id((("lex", t), i))] = (t, i)

    def canon_py(lit):
        v = abs(lit)
        return (lit > 0, "x", v - 1) if v <= m else (lit > 0, "a", *aux[v])

    py = [sorted(canon_py(l) for l in c) for c in col.out]
    ln = [sorted(canon_lean(l) for l in c) for c in lean_lex]
    taut = [c for c in py
            if any((not s, k, *r) in c for (s, k, *r) in c)]
    py_nt = [c for c in py if c not in taut]
    same = sorted(map(str, py_nt)) == sorted(map(str, ln))
    print(f"[lexdiff] {args.key}: pysat {len(py)} lex clauses "
          f"({len(taut)} tautological, omitted by Lean), Lean {len(ln)}")
    print(f"[lexdiff] in pysat not in Lean: "
          f"{sum(1 for c in py_nt if c not in ln)}")
    print(f"[lexdiff] in Lean not in pysat: "
          f"{sum(1 for c in ln if c not in py_nt)}")
    print(f"[lexdiff] {'MATCH' if same else 'MISMATCH'}")
    return 0 if same else 1


if __name__ == "__main__":
    sys.exit(main())
