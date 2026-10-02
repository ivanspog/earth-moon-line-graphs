#!/usr/bin/env python3
"""Write the DIMACS file of a Lean-defined formula WITHOUT running Lean.

`lake exe biplanar-export` initialises every registered instance at start-up
(each `ws`/`F` is a closed term), so one export costs ~60 s and ~5 GB once the
registry holds the certified instances (F-038 §8), and the cost grows with
every instance. This script prints the same bytes from the same inputs, for

  * mkCNFSym₀ G ws gens               (Biplanar/SymDefs.lean), and
  * Cube.leafCNF cube (mkCNFSym₀ …)   (LRATCatcher, cube unit clauses first),

mirroring the Lean definitions exactly: the part-swap unit `[(0, false)]`;
`lexAll m m gens` (per generator t, `lexClauses m (m + t·m) eperm`: the unit
on the first activity variable, then per position i the clause
`¬aᵢ ∨ ¬xᵢ ∨ y_i` — OMITTED where eperm fixes i (the tautology trap) — and,
for i + 1 < m, the two chain clauses); then `ws.map Witness.clause`
(`idx.map (i, !pol)`, in witness-line order); printed as
`Std.Sat.CNF.dimacs` does (`p cnf <max var + 1> <#clauses>`, each literal
followed by a space, then `0`).

Nothing here is trusted: Lean checks the certificate against ITS OWN term, so
a divergence can only make the Lean build fail. `--selftest` compares the
output byte for byte with CNFs the Lean exporter wrote (SHA-256s recorded in
population/f034-a4-cert/), which is what makes a divergence unlikely.

Usage:
  lean_cnf_writer.py --graph graph.json --witnesses w.txt --out leaf.cnf [--cube L1 L2 ...]
  lean_cnf_writer.py --selftest
"""
import argparse
import hashlib
import json
import os
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def lit(v, pol):
    """0-based variable v with polarity pol -> DIMACS literal."""
    return v + 1 if pol else -(v + 1)


def lex_clauses(m, base, ep):
    yield [lit(base, True)]
    for i in range(m):
        y = ep[i] if i < len(ep) else i          # ep.getD i i
        if y != i:
            yield [lit(base + i, False), lit(i, False), lit(y, True)]
        if i + 1 < m:
            yield [lit(base + i, False), lit(i, True), lit(y, True), lit(base + i + 1, True)]
            yield [lit(base + i, False), lit(i, False), lit(y, False), lit(base + i + 1, True)]


def parse_witness_line(line):
    """Mirror of Biplanar.parseLine: returns (pol, idx) or None (Lean drops it)."""
    t = [int(x) for x in line.split()]
    try:
        pol, ne = t[0], t[1]
        idx = t[2:2 + ne]
        rest = t[2 + ne:]
        if len(idx) != ne:
            return None
        kind, nb = rest[0], rest[1]
        rest = rest[2 + nb:]
        npaths = rest[0]
        rest = rest[1:]
        for _ in range(npaths):
            ln = rest[0]
            if len(rest) < 1 + ln:
                return None
            rest = rest[1 + ln:]
        if rest:
            return None
    except IndexError:
        return None
    return pol == 1, idx


def clauses(m, gens, witness_path, cube=()):
    for l in cube:                                   # Cube.leafCNF: cube units first
        yield [l]
    yield [lit(0, False)]                            # part-swap unit
    for t, g in enumerate(gens):                     # lexAll m m gens
        yield from lex_clauses(m, m + t * m, g["eperm"])
    with open(witness_path) as f:                    # ws.map Witness.clause
        for line in f:
            if not line.strip():
                continue
            w = parse_witness_line(line)
            assert w is not None, f"witness line Lean would DROP (renumbering!): {line[:80]}"
            pol, idx = w
            yield [lit(i, not pol) for i in idx]


def write(out, m, gens, witness_path, cube=()):
    """Two passes: the header needs the clause count and the largest variable."""
    n = maxv = 0
    for c in clauses(m, gens, witness_path, cube):
        n += 1
        for x in c:
            if abs(x) > maxv:
                maxv = abs(x)
    with open(out, "w") as f:
        f.write(f"p cnf {maxv} {n}\n")
        for c in clauses(m, gens, witness_path, cube):
            f.write("".join(f"{x} " for x in c) + "0\n")
    return n


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def selftest():
    """Byte-compare with CNFs the Lean exporter wrote for certified instances."""
    import tempfile
    cert = os.path.join(ROOT, "population", "f034-a4-cert")
    ok = bad = 0
    rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(cert, "metrics.tsv"))]
    lean_sha = {i: v for i, k, v in rows if k == "lean_cnf_sha256"}
    cf = {i: v for i, k, v in rows if k == "counter_free"}
    tmp = tempfile.mkdtemp()
    for i, want in sorted(lean_sha.items()):
        if cf.get(i) != "True":
            continue
        gdir = os.path.join(cert, f"m{i}", "core" if os.path.isdir(os.path.join(cert, f"m{i}", "core"))
                            else "resolve")
        g = json.load(open(os.path.join(gdir, "graph.json")))
        w = os.path.join(ROOT, "lean", "data", f"a4_m{i}", "witnesses.txt")
        out = os.path.join(tmp, f"m{i}.cnf")
        write(out, len(g["edges"]), g["gens"], w)
        got = sha(out)
        os.remove(out)
        same = got == want
        ok += same
        bad += not same
        print(f"  a4_m{i}: {'MATCH' if same else 'DIFF'}")
    for d in sorted(x for x in os.listdir(cert) if x.startswith("split-m")):
        mp = os.path.join(cert, d, "split_metrics.json")
        if not os.path.exists(mp):
            continue
        M = json.load(open(mp))
        if not M.get("lean"):
            continue
        g = json.load(open(os.path.join(cert, d, "c1", "graph.json")))
        cubes = json.load(open(os.path.join(cert, d, "cubes.json")))
        for j, cube in enumerate(cubes, 1):
            t = M["lean"].get(f"leaf{j}")
            if not t or "exported_by" in t and t["exported_by"] != "lean":
                continue
            out = os.path.join(tmp, "leaf.cnf")
            write(out, len(g["edges"]), g["gens"],
                  os.path.join(ROOT, "lean", "data", M["key"], f"w{j}.txt"), cube)
            same = sha(out) == t["cnf_sha256"]
            os.remove(out)
            ok += same
            bad += not same
            print(f"  {M['key']} leaf{j} (cube {cube}): {'MATCH' if same else 'DIFF'}")
    print(f"[writer selftest] {ok} byte-identical, {bad} different")
    return 0 if bad == 0 and ok > 0 else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph")
    ap.add_argument("--witnesses")
    ap.add_argument("--out")
    ap.add_argument("--cube", nargs="*", type=int, default=[])
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    g = json.load(open(a.graph))
    n = write(a.out, len(g["edges"]), g["gens"], a.witnesses, a.cube)
    print(f"lean_cnf_writer: wrote {n} clauses to {a.out}"
          + (f" (cube of {len(a.cube)} literals)" if a.cube else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
