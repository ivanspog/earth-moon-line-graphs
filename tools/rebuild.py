#!/usr/bin/env python3
"""Rebuild the Lean non-biplanarity theorems from this repository alone.

The LRAT certificates are not stored (several GB); they are regenerated. For
each instance this script

  1. reads the graph G and the symmetry generators from the instance's Lean
     source (Defs.lean or Base.lean), and the cubes from Cubes.lean (split
     instances), so the formula is derived from exactly the text Lean checks;
  2. writes each formula's DIMACS file with verifier/lean_cnf_writer.py (the
     clause list of Biplanar.mkCNFSym₀ G ws gens, with the cube's unit clauses
     first for a leaf) and compares its SHA-256 with the instance's MANIFEST,
     recorded when the theorem was first certified  [--check-cnf];
  3. runs CaDiCaL to produce the LRAT certificate at the path the Lean file
     reads (lean/data/<key>/F.lrat or leaf<j>.lrat)  [--solve];
  4. runs `lake build` on the leaves (in batches), the cover and the main
     module, and checks the build output: "Build completed successfully", no
     "error", and the axioms of `<instance>.not_biplanar` are only propext,
     Classical.choice, Quot.sound and native_decide auxiliaries  [--build].

Nothing here is trusted: Lean re-checks every certificate against its own
formula, so a wrong CNF or LRAT can only make a build fail. Step 2 shows that
the published witness files reproduce the certified formulas byte for byte.

Run tools/unpack_witnesses.sh first.

Usage:
  python tools/rebuild.py --all --check-cnf                 # minutes; no solver needed
  python tools/rebuild.py A4M01 --check-cnf --solve --build # one instance end to end
  python tools/rebuild.py --all --check-cnf --solve --build --lean-jobs 2
Options: --cadical PATH (default: cadical on PATH), --keep (keep LRAT/CNF files).
Resources: CaDiCaL takes 20 s to ~20 min per formula on one core; a leaf's
`lake build` needs up to ~6 GB of memory (the certificate is imported).
"""
import argparse
import glob
import hashlib
import os
import re
import subprocess
import sys
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
LEAN = os.path.join(ROOT, "lean")
INST = os.path.join(LEAN, "Biplanar", "Instances")
sys.path.insert(0, os.path.join(ROOT, "verifier"))
import lean_cnf_writer  # noqa: E402

STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NATIVE = re.compile(r"^[A-Za-z_][A-Za-z0-9_₀-₉']*\._native\.native_decide\.ax_\d+_\d+$")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def instance(name):
    """Formulas of an instance: (tag, witness file, DIMACS cube, cnf path, lrat path)."""
    d = os.path.join(INST, name)
    split = os.path.exists(os.path.join(d, "Base.lean"))
    src = open(os.path.join(d, "Base.lean" if split else "Defs.lean")).read()
    g = re.search(r"def G : Biplanar\.Graph := ⟨(\d+), \[(.*?)\]⟩", src, re.S)
    m = len(re.findall(r"\((\d+), (\d+)\)", g.group(2)))
    gsrc = src[src.index("def gens"):]
    gens = [{"eperm": [int(x) for x in ep.split(",") if x.strip()]}
            for _, ep in re.findall(r"⟨\[([0-9, ]*)\],\s*\[([0-9, ]*)\]⟩", gsrc)]
    if split:
        w1 = open(os.path.join(d, "W1.lean")).read()
        key = re.search(r'include_str\s+"[./]*data/([^/]+)/w1\.txt"', w1).group(1)
        csrc = open(os.path.join(d, "Cubes.lean")).read()
        cubes = {int(j): [(int(v) + 1) * (1 if p == "true" else -1)
                          for v, p in re.findall(r"\((\d+), (true|false)\)", body)]
                 for j, body in re.findall(r"def cube(\d+) : LRATCatcher\.Cube := \[(.*?)\]\n", csrc)}
        forms = [(f"leaf{j}", f"w{j}.txt", cubes[j]) for j in sorted(cubes)]
    else:
        key = re.search(r'include_str\s+"[./]*data/([^/]+)/witnesses\.txt"', src).group(1)
        forms = [("F", "witnesses.txt", [])]
    ddir = os.path.join(LEAN, "data", key)
    out = [(tag, os.path.join(ddir, w), cube, os.path.join(ddir, f"{tag}.cnf"), os.path.join(ddir, f"{tag}.lrat"))
           for tag, w, cube in forms]
    return {"name": name, "key": key, "split": split, "m": m, "gens": gens, "forms": out, "ddir": ddir}


def manifest(ddir):
    want = {}
    for line in open(os.path.join(ddir, "MANIFEST.txt")):
        if line.startswith("#") or not line.strip():
            continue
        h, rel = line.split()[:2]
        want[os.path.basename(rel)] = h
    return want


def lake_build(targets, log):
    t0 = time.time()
    p = subprocess.run(["lake", "build", *targets], cwd=LEAN, capture_output=True, text=True)
    out = p.stdout + p.stderr
    with open(log, "a") as f:
        f.write(out)
    ok = p.returncode == 0 and "error" not in out and "Build completed successfully" in out
    return ok, out, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("names", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--check-cnf", action="store_true")
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--lean-jobs", type=int, default=2, help="leaves per lake build call")
    ap.add_argument("--cadical", default="cadical")
    ap.add_argument("--keep", action="store_true")
    a = ap.parse_args()
    names = (sorted(os.path.basename(p)[:-5] for p in glob.glob(os.path.join(INST, "A4M*.lean")))
             if a.all else a.names)
    if not names:
        ap.error("give instance names or --all")
    logdir = os.path.join(ROOT, "rebuild-logs")
    os.makedirs(logdir, exist_ok=True)
    bad = 0
    for name in names:
        I = instance(name)
        want = manifest(I["ddir"])
        print(f"== {name} ({I['key']}): {len(I['forms'])} formula(s), m = {I['m']} edges, "
              f"{len(I['gens'])} generators", flush=True)
        for tag, w, cube, cnf, lrat in I["forms"]:
            if not os.path.exists(w):
                sys.exit(f"missing {w}: run tools/unpack_witnesses.sh first")
            if a.check_cnf or a.solve:
                n = lean_cnf_writer.write(cnf, I["m"], I["gens"], w, cube)
                got = sha(cnf)
                exp = want.get(f"{tag}.cnf")
                same = got == exp
                bad += not same
                print(f"   {tag}: {n} clauses, CNF SHA-256 {'MATCHES' if same else 'DIFFERS FROM'} the MANIFEST",
                      flush=True)
            if a.solve:
                t0 = time.time()
                rc = subprocess.run([a.cadical, "--lrat", "--no-binary", "--no-factor", "-q", cnf, lrat]).returncode
                if rc != 20:
                    bad += 1
                    print(f"   {tag}: CaDiCaL rc {rc} (expected 20 = UNSAT)", flush=True)
                else:
                    print(f"   {tag}: UNSAT, LRAT {os.path.getsize(lrat) / 1e9:.2f} GB, {time.time() - t0:.0f} s",
                          flush=True)
            if (a.check_cnf or a.solve) and not a.keep and os.path.exists(cnf):
                os.remove(cnf)
        if a.build:
            log = os.path.join(logdir, f"{name}.log")
            open(log, "w").close()
            mod = f"Biplanar.Instances.{name}"
            steps = []
            if I["split"]:
                L = len(I["forms"])
                steps += [[f"{mod}.Leaf{j}" for j in range(b, min(b + a.lean_jobs, L + 1))]
                          for b in range(1, L + 1, a.lean_jobs)]
                steps.append([f"{mod}.Cover"])
            steps.append([mod])
            out = ""
            for t in steps:
                ok, out, dt = lake_build(t, log)
                print(f"   lake build {t[0]}{'…' if len(t) > 1 else ''}: {'OK' if ok else 'FAILED'} ({dt:.0f} s)",
                      flush=True)
                if not ok:
                    bad += 1
                    break
            else:
                ax = re.search(rf"'Biplanar\.{name}\.not_biplanar' depends on axioms: \[(.*?)\]",
                               out.replace("\n", " "))
                axioms = [x.strip() for x in ax.group(1).split(",")] if ax else []
                odd = [x for x in axioms if x not in STD_AXIOMS and not NATIVE.match(x)]
                if not axioms or odd:
                    bad += 1
                    print(f"   AXIOMS NOT AS EXPECTED: {odd or 'no axiom line'}", flush=True)
                else:
                    nd = len(axioms) - len(STD_AXIOMS & set(axioms))
                    print(f"   Biplanar.{name}.not_biplanar: built; axioms = standard + {nd} native_decide",
                          flush=True)
            if not a.keep:
                for _, _, _, _, lrat in I["forms"]:
                    if os.path.exists(lrat):
                        os.remove(lrat)
    print(f"=== {len(names)} instance(s), {bad} problem(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
