#!/usr/bin/env python3
"""F-038 final audit: is every A4 member covered by a Lean theorem about the
RIGHT graph, with the RIGHT statement, that really BUILT?

The certification pipelines (monolithic chain, split route, per-cube search,
static-from-dump; the cloud orchestration around them) are untrusted: a bug
there can only make a Lean build fail, provided three things hold for the
instance that did build. This script checks those three things from the
artefacts, on code paths independent of the pipelines:

  1. Right graph. The multiplicities in the instance's doc line equal the
     member's in (a) the enumeration, recomputed from f033_line_graph_route.py
     (`f034_a4_line_graph_sat.py --list --recompute`, which also asserts the
     cache agrees), and (b) the original UNSAT run's log
     population/f034-a4/member-<i>.log; and the `def G` literal is isomorphic
     to L(M) (networkx line_graph of the MultiGraph, not the solver's build()).
  2. Right statement. `theorem not_biplanar` reads exactly
         (planar) (H2 : Kuratowski's easy direction) (H3 : IsoInvariant G planar)
           : ¬ Biplanar.Biplanar planar G
     inside `namespace Biplanar.A4M<i><route>`, `def G` occurs once among the
     instance's files (in its Defs/Base module), and no file of the instance
     contains sorry/admit/axiom/unsafe/implemented_by/extern/opaque, a
     macro/syntax/notation/elab, or a set_option other than maxHeartbeats.
  3. Really built. The main build log says "Build completed successfully",
     contains no "error", and prints
         'Biplanar.A4M<i><route>.not_biplanar' depends on axioms: [...]
     with only propext, Classical.choice, Quot.sound and native_decide
     auxiliaries (`<decl>._native.native_decide.ax_<k>_<l>`). The witness
     files the module includes (include_str) still have the SHA-256 recorded
     in its MANIFEST at build time.

Trusted, not re-checked here: the Lean kernel and compiler (native_decide),
Biplanar/{Basic,SymDefs,Sym,Lift}.lean (LEAN-1/2; their SHA-256s are printed so
two machines can be compared), and LRAT-Catcher.

Usage: .venv/bin/python verifier/f038_a4_audit.py [--allow-missing]
Exit 0 iff every instance found passes and (unless --allow-missing) all 22
members are covered.
"""
import glob
import hashlib
import os
import re
import subprocess
import sys

import networkx as nx

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
INST = os.path.join(ROOT, "lean", "Biplanar", "Instances")
CERT = os.path.join(ROOT, "population", "f034-a4-cert")
STATEMENT = ("theorem not_biplanar (planar : List Biplanar.Edge → Prop) "
             "(H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) "
             "(H3 : Biplanar.IsoInvariant G planar) : ¬ Biplanar.Biplanar planar G :=")
FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"^\s*(private\s+|noncomputable\s+)*axiom\b", r"\bunsafe\b",
             r"implemented_by", r"@\[\s*extern", r"\bopaque\b",
             r"^\s*(local\s+|scoped\s+)?(macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|"
             r"infixr|prefix|postfix)\b", r"\binstance\b"]
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NATIVE = re.compile(r"^[A-Za-z_][A-Za-z0-9_₀-₉']*\._native\.native_decide\.ax_\d+_\d+$")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def toks(mults):
    return sorted(mults.split())


def enumeration():
    out = subprocess.run([sys.executable,
                          os.path.join(ROOT, "verifier", "f034_a4_line_graph_sat.py"), "--list", "--recompute"],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    rows = {}
    for line in out.strip().splitlines():
        i, slack, e, *mu = line.split()
        rows[int(i)] = (int(e), " ".join(mu))
    assert sorted(rows) == list(range(22)), f"enumeration has {len(rows)} members, expected 22"
    return rows


def original_run(i):
    src = open(os.path.join(ROOT, "population", "f034-a4", f"member-{i:02d}.log")).read()
    mults = re.search(r"mults=\[([^\]]*)\]", src).group(1)
    unsat = re.search(r"^RESULT \S+ UNSAT", src, re.M) is not None
    return mults, unsat


def build_log(i, route):
    """(main build log text, path) for an instance, by route."""
    f = {"": [f"m{i:02d}/lean-build.log", f"m{i:02d}/axioms.txt"],
         "S": [f"split-m{i:02d}/build-main.log"],
         "C": [f"cs-a4_m{i:02d}c/build-main.log"],
         "R": [f"cs-a4_m{i:02d}r/build-main.log"]}[route]
    paths = [os.path.join(CERT, p) for p in f]
    if not os.path.exists(paths[0]):
        return None, paths[0]
    return "\n".join(open(p).read() for p in paths if os.path.exists(p)), paths[0]


def audit(i, route, enum):
    name = f"A4M{i:02d}{route}"
    key = f"a4_m{i:02d}{route.lower()}"
    errs = []
    main = os.path.join(INST, name + ".lean")
    files = [main] + sorted(glob.glob(os.path.join(INST, name, "*.lean")))
    gfile = os.path.join(INST, name, "Defs.lean" if route == "" else "Base.lean")
    srcs = {p: open(p).read() for p in files}
    # 1. right graph
    e_enum, mu_enum = enum[i]
    mu_orig, orig_unsat = original_run(i)
    m = re.search(r"multiplicities \[([^\]]*)\]", srcs[gfile])
    mu_lean = m.group(1) if m else ""
    if not orig_unsat:
        errs.append("original run did not end UNSAT")
    if not (toks(mu_lean) == toks(mu_enum) == toks(mu_orig)):
        errs.append(f"multiplicities differ: lean [{mu_lean}] enum [{mu_enum}] orig [{mu_orig}]")
    g = re.search(r"def G : Biplanar\.Graph := ⟨(\d+), \[(.*?)\]⟩", srcs[gfile], re.S)
    if not g:
        errs.append("no `def G` literal in " + os.path.basename(gfile))
    else:
        E = [tuple(map(int, t)) for t in re.findall(r"\((\d+), (\d+)\)", g.group(2))]
        G = nx.Graph()
        G.add_nodes_from(range(int(g.group(1))))
        G.add_edges_from(E)
        M = nx.MultiGraph()
        for t in mu_enum.split():
            uv, k = t.split(":")
            M.add_edges_from([(int(uv[0]), int(uv[1]))] * int(k))
        L = nx.Graph(nx.line_graph(M))
        if not (len(E) == len(set(E)) == e_enum and all(u < v < G.number_of_nodes() for u, v in E)
                and G.number_of_nodes() == 28 and nx.is_isomorphic(G, L)):
            errs.append(f"G (n={G.number_of_nodes()}, e={len(E)}) is not L(M) (e={L.number_of_edges()})")
    # 2. right statement, nothing smuggled in
    s = re.search(r"theorem not_biplanar\b.*?:=", srcs[main], re.S)
    if not s or " ".join(s.group(0).split()) != STATEMENT:
        errs.append("theorem statement differs from the standard one: "
                    + (" ".join(s.group(0).split())[:200] if s else "missing"))
    for p, src in srcs.items():
        if f"namespace Biplanar.{name}\n" not in src:
            errs.append(f"{os.path.basename(p)}: not in namespace Biplanar.{name}")
        for pat in FORBIDDEN:
            for hit in re.finditer(pat, src, re.M):
                errs.append(f"{os.path.basename(p)}: forbidden `{hit.group(0).strip()}`")
        for so in re.findall(r"set_option\s+(\S+)", src):
            if so != "maxHeartbeats":
                errs.append(f"{os.path.basename(p)}: set_option {so}")
    ndefs = sum(len(re.findall(r"^def G\b", src, re.M)) for src in srcs.values())
    if ndefs != 1 or not re.search(r"^def G\b", srcs[gfile], re.M):
        errs.append(f"`def G` occurs {ndefs} times (want once, in {os.path.basename(gfile)})")
    # 3. really built
    log, lpath = build_log(i, route)
    nax = 0
    if log is None:
        errs.append(f"no build log {os.path.relpath(lpath, ROOT)}")
    else:
        flat = log.replace("\n", " ")
        if "Build completed successfully" not in log:
            errs.append("build log lacks 'Build completed successfully'")
        if "error" in log:
            errs.append(f"build log contains 'error' ({log.count('error')}x)")
        ax = re.search(rf"'Biplanar\.{name}\.not_biplanar' depends on axioms: \[(.*?)\]", flat)
        if not ax:
            errs.append(f"no axiom line for Biplanar.{name}.not_biplanar")
        else:
            axioms = [x.strip() for x in ax.group(1).split(",")]
            bad = [x for x in axioms if x not in STD_AXIOMS and not NATIVE.match(x)]
            nax = len(axioms) - len(STD_AXIOMS & set(axioms))
            if bad:
                errs.append(f"unexpected axioms: {bad[:5]}")
    # witness files unchanged since the build
    ddir = os.path.join(ROOT, "lean", "data", key)
    mf = os.path.join(ddir, "MANIFEST.txt")
    nw = 0
    if not os.path.exists(mf):
        errs.append("no MANIFEST.txt")
    else:
        want = {}
        for line in open(mf):
            if line.startswith("#") or "(deleted)" in line or not line.strip():
                continue
            h, rel = line.split()[:2]
            want[os.path.basename(rel)] = h
        incl = set(re.findall(rf'include_str\s+"[./]*data/{key}/([^"]+)"', "\n".join(srcs.values())))
        if route == "":
            incl.add("witnesses.txt")
        for fn in sorted(incl):
            p = os.path.join(ddir, fn)
            if fn not in want:
                errs.append(f"{fn}: included but not in MANIFEST")
            elif not os.path.exists(p):
                errs.append(f"{fn}: missing")
            elif sha(p) != want[fn]:
                errs.append(f"{fn}: SHA-256 differs from MANIFEST")
            else:
                nw += 1
        nleaf = len([p for p in files if re.search(r"/Leaf\d+\.lean$", p)])
        if route and nw != nleaf:
            errs.append(f"{nw} verified witness files for {nleaf} leaves")
    return name, errs, nax, nw


def main():
    allow_missing = "--allow-missing" in sys.argv
    print("trusted core (compare across machines):")
    for f in ("Basic", "SymDefs", "Sym", "Lift"):
        print(f"  {sha(os.path.join(ROOT, 'lean', 'Biplanar', f + '.lean'))[:16]}  Biplanar/{f}.lean")
    enum = enumeration()
    print("enumeration recomputed: 22 members, cache agrees")
    found = {}
    for d in sorted(os.listdir(INST)):
        mm = re.fullmatch(r"A4M(\d\d)([SCR]?)\.lean", d)
        if mm:
            found.setdefault(int(mm.group(1)), []).append(mm.group(2))
    fails = 0
    covered = []
    for i in range(22):
        ok_routes = []
        for route in found.get(i, []):
            name, errs, nax, nw = audit(i, route, enum)
            if errs:
                fails += 1
                print(f"  member {i:02d}  {name:8s}  FAIL")
                for e in errs:
                    print(f"        - {e}")
            else:
                ok_routes.append(name)
                print(f"  member {i:02d}  {name:8s}  OK   ({nax} native_decide axioms, {nw} witness file(s) "
                      f"match MANIFEST)")
        if ok_routes:
            covered.append(i)
        else:
            print(f"  member {i:02d}  --        NOT CERTIFIED")
    missing = [i for i in range(22) if i not in covered]
    print(f"=== {len(covered)}/22 members covered by an audited Lean theorem; {fails} failing instance(s)"
          + (f"; missing {missing}" if missing else ""))
    return 1 if fails or (missing and not allow_missing) else 0


if __name__ == "__main__":
    sys.exit(main())
