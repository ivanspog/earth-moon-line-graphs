#!/usr/bin/env python3
"""Independent scan of a DIMACS file for the TAUTOLOGY TRAP: Lean's verified
LRAT checker silently drops tautological clauses (a literal and its negation)
while converting a CNF, which renumbers every later clause and invalidates the
certificate. Exit 1 if any clause is tautological. Also reports clauses with a
repeated literal (harmless, but worth knowing).

Usage: cnf_tautology_scan.py F.cnf
"""
import sys

bad = rep = n = 0
for line in open(sys.argv[1]):
    if line.startswith(("p", "c")):
        continue
    lits = [int(t) for t in line.split()[:-1]]
    s = set(lits)
    n += 1
    bad += any(-l in s for l in s)
    rep += len(s) != len(lits)
print(f"[taut] {sys.argv[1]}: {bad} tautological clauses"
      + (f" ({rep} with a repeated literal)" if rep else "") + f" of {n}")
sys.exit(1 if bad else 0)
