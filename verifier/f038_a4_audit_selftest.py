#!/usr/bin/env python3
"""Mutation test of verifier/f038_a4_audit.py: an audit that passes everything
proves nothing, so break one artefact at a time in a scratch copy of two
certified instances (A4M01, monolithic; A4M14S, split) and check that the
audit FAILS each mutant with the expected reason, and passes the clean copy.

Usage: .venv/bin/python verifier/f038_a4_audit_selftest.py [scratch-dir]
"""
import importlib.util
import os
import re
import shutil
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
spec = importlib.util.spec_from_file_location("audit", os.path.join(ROOT, "verifier", "f038_a4_audit.py"))
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)

INSTANCES = [(1, ""), (14, "S")]


def copy_tree(dst):
    for rel in ("lean/Biplanar/Instances/A4M01.lean", "lean/Biplanar/Instances/A4M01",
                "lean/data/a4_m01", "population/f034-a4-cert/m01",
                "lean/Biplanar/Instances/A4M14S.lean", "lean/Biplanar/Instances/A4M14S",
                "lean/data/a4_m14s", "population/f034-a4-cert/split-m14",
                "population/f034-a4/member-01.log", "population/f034-a4/member-14.log"):
        s, d = os.path.join(ROOT, rel), os.path.join(dst, rel)
        os.makedirs(os.path.dirname(d), exist_ok=True)
        (shutil.copytree if os.path.isdir(s) else shutil.copy)(s, d)


def edit(path, old, new, count=1):
    src = open(path).read()
    assert old in src, f"mutation anchor not found in {path}: {old[:60]!r}"
    open(path, "w").write(src.replace(old, new, count))


def append(path, text):
    open(path, "a").write(text)


I = "lean/Biplanar/Instances/"
MUTANTS = [
    # (instance, description, mutation(dst), expected substring of an error)
    ((1, ""), "doc multiplicities changed", lambda d: edit(d + I + "A4M01/Defs.lean", "14:4 15:2", "14:4 15:3"),
     "multiplicities differ"),
    ((1, ""), "one edge of G changed", lambda d: edit(d + I + "A4M01/Defs.lean", "(0, 1), ", "(0, 27), "),
     "is not L(M)"),
    ((14, "S"), "one edge of G dropped", lambda d: edit(d + I + "A4M14S/Base.lean", "(0, 1), ", ""),
     "is not L(M)"),
    ((1, ""), "H3 dropped from the statement",
     lambda d: edit(d + I + "A4M01.lean", "    (H3 : Biplanar.IsoInvariant G planar) :\n", "    :\n"),
     "statement differs"),
    ((14, "S"), "conclusion weakened to True",
     lambda d: edit(d + I + "A4M14S.lean", "¬ Biplanar.Biplanar planar G :=", "True :="),
     "statement differs"),
    ((1, ""), "sorry inserted", lambda d: append(d + I + "A4M01/Defs.lean", "\ntheorem t : 1 = 2 := sorry\n"),
     "forbidden `sorry`"),
    ((14, "S"), "axiom declared in a leaf", lambda d: append(d + I + "A4M14S/Leaf2.lean", "\naxiom cheat : False\n"),
     "forbidden `axiom`"),
    ((1, ""), "kernel check switched off",
     lambda d: edit(d + I + "A4M01.lean", "set_option maxHeartbeats 2000000",
                    "set_option maxHeartbeats 2000000\nset_option debug.skipKernelTC true"),
     "set_option debug.skipKernelTC"),
    ((14, "S"), "notation that could rebind a symbol",
     lambda d: append(d + I + "A4M14S/Cubes.lean", "\nnotation \"G'\" => G\n"), "forbidden `notation`"),
    ((1, ""), "second def G", lambda d: edit(d + I + "A4M01.lean", "lrat_reflect_cnf",
                                             "def G : Biplanar.Graph := ⟨1, []⟩\n\nlrat_reflect_cnf"),
     "`def G` occurs 2 times"),
    ((1, ""), "build log without success line",
     lambda d: edit(d + "population/f034-a4-cert/m01/lean-build.log", "Build completed successfully", "Build ok"),
     "lacks 'Build completed successfully'"),
    ((14, "S"), "error in the build log",
     lambda d: append(d + "population/f034-a4-cert/split-m14/build-main.log", "\nerror: something\n"),
     "contains 'error'"),
    ((1, ""), "foreign axiom printed",
     lambda d: [edit(d + "population/f034-a4-cert/m01/" + f, "[propext,", "[cheat, propext,")
                for f in ("lean-build.log", "axioms.txt")], "unexpected axioms"),
    ((14, "S"), "axiom line names another theorem",
     lambda d: edit(d + "population/f034-a4-cert/split-m14/build-main.log", "'Biplanar.A4M14S.not_biplanar'",
                    "'Biplanar.A4M14S.other'"), "no axiom line"),
    ((1, ""), "witness file edited after the build",
     lambda d: append(d + "lean/data/a4_m01/witnesses.txt", "\n"), "witnesses.txt: SHA-256 differs"),
    ((14, "S"), "witness file of a leaf missing",
     lambda d: os.remove(d + "lean/data/a4_m14s/w3.txt"), "w3.txt: missing"),
    ((14, "S"), "build log missing",
     lambda d: os.remove(d + "population/f034-a4-cert/split-m14/build-main.log"), "no build log"),
]


def run(dst, enum, inst):
    A.ROOT = dst
    A.INST = os.path.join(dst, "lean", "Biplanar", "Instances")
    A.CERT = os.path.join(dst, "population", "f034-a4-cert")
    return A.audit(inst[0], inst[1], enum)


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else tempfile.mkdtemp()
    A.ROOT = ROOT
    enum = A.enumeration()
    bad = 0
    clean = os.path.join(base, "clean") + "/"
    copy_tree(clean)
    for inst in INSTANCES:
        name, errs, _, _ = run(clean, enum, inst)
        ok = not errs
        bad += not ok
        print(f"{'PASS' if ok else 'FAIL'}  clean copy of {name} passes" + ("" if ok else f": {errs}"))
    for k, (inst, desc, mutate, want) in enumerate(MUTANTS):
        d = os.path.join(base, f"mut{k}") + "/"
        copy_tree(d)
        mutate(d)
        name, errs, _, _ = run(d, enum, inst)
        ok = any(want in e for e in errs)
        bad += not ok
        print(f"{'PASS' if ok else 'FAIL'}  {name}: {desc} -> caught" if ok else
              f"FAIL  {name}: {desc} -> NOT caught as {want!r}; errors: {errs}")
        shutil.rmtree(d)
    shutil.rmtree(clean)
    print(f"=== {bad} failure(s) of {len(INSTANCES) + len(MUTANTS)}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
