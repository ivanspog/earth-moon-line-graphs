#!/usr/bin/env python3
"""Idempotent edits of lean/Biplanar/Instances.lean, the registry that
`lake exe biplanar-export` reads (one `("<key>", Biplanar.<Name>.F)` entry and
one `import Biplanar.Instances.<Name>.Defs` per instance).

Usage:
  lean_registry.py add <key> <Name> [--module Biplanar.Instances.<Name>.Defs] [--term Biplanar.<Name>.F]
The split route registers one formula per leaf, e.g.
  lean_registry.py add a4_m17s_3 A4M17S --module Biplanar.Instances.A4M17S.W3 --term Biplanar.A4M17S.F3
"""
import argparse
import os

P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "Biplanar",
                 "Instances.lean")


def add(key, module, term):
    s = open(P).read()
    imp = f"import {module}\n"
    if imp not in s:
        last = s.rindex("import Biplanar.Instances.")
        eol = s.index("\n", last) + 1
        s = s[:eol] + imp + s[eol:]
    ent = f'("{key}", {term})'
    if ent not in s:
        assert f'("{key}",' not in s, f"key {key} already registered with another term"
        s = s.replace(")]\n\ndef lookup", f"),\n   {ent}]\n\ndef lookup", 1)
        assert ent in s, "registry table not found"
    open(P, "w").write(s)


def remove(key, module=None):
    s = open(P).read()
    import re
    s2 = re.sub(r',\n   \("' + re.escape(key) + r'", [^)]*\)', "", s)
    if module:
        s2 = s2.replace(f"import {module}\n", "")
    open(P, "w").write(s2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["add", "remove"])
    ap.add_argument("key")
    ap.add_argument("name")
    ap.add_argument("--module")
    ap.add_argument("--term")
    a = ap.parse_args()
    if a.cmd == "remove":
        remove(a.key, a.module)
    else:
        add(a.key, a.module or f"Biplanar.Instances.{a.name}.Defs", a.term or f"Biplanar.{a.name}.F")


if __name__ == "__main__":
    main()
