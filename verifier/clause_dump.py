"""Clause dump writer for the Lean-verification milestone (P1).

Every clause the biplanarity encoding relies on beyond the cardinality
constraints — pre-seeded K5/K3,3 splits and every propagator-emitted
Kuratowski clause — is written to a JSONL file together with an explicit
subdivision certificate (`kuratowski_cert.py`), validated at write time.
The dump is the feed for `lean_static_resolve.py` (static re-solve + LRAT
core) and, through it, for the Lean Lift lemma.

Line 1 is a provenance header:
  {"type": "header", "script": ..., "git": ..., "time": ..., "name": ...,
   "n": n, "m": m, "edges": [[u,v],...], "cap": 3n-6, "sym_on": bool,
   "extra_units": [...], "check_at": k,
   "gens": [{"vperm": [...n...], "eperm": [...m...]}, ...]}

`gens` records the automorphism generators whose lex symmetry-breaking
clauses were added to the solver, in the order their activity variables
were allocated -- one vertex permutation and the induced edge-index
permutation each. It is what makes a SYM-ON dump liftable to Lean at all:
`lean/Biplanar/SymDefs.lean::Gen.ok` re-checks each pair against the graph
and `Biplanar.not_biplanar_of_unsat_sym` proves the lex clauses sound
(hypothesis (H3), planarity is an isomorphism invariant). A sym-on dump
without `gens` is refused downstream.
then one line per clause:
  {"t": "preseed"|"prop"|"model", "pol": 0|1, "e": [edge indices, 0-based],
   "c": {"kind": "K5"|"K33", "branch": [...], "paths": [[...], ...]}}
pol = 1 means the clause forbids "all these edges in part 2" (negative
literals on the 1-based edge variables), pol = 0 forbids "all in part 1".

The writer only ever REJECTS: an invalid certificate raises and aborts the
run (`AssertionError`), it never silently drops or accepts a clause.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
from kuratowski_cert import certificate_valid, norm_edge  # noqa: E402


def _git_head():
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=os.path.dirname(__file__),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return None


class ClauseDump:
    def __init__(self, path, n, edges, cap, name, sym_on, extra_units,
                 check_at, script, gens=None):
        self.edges = [tuple(sorted(e)) for e in edges]
        self.eidx = {e: i for i, e in enumerate(self.edges)}
        self.count = {"preseed": 0, "prop": 0, "model": 0}
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        self.f = open(path, "w", buffering=1)  # line-buffered: kill-safe
        self.path = path
        header = {"type": "header", "script": script, "git": _git_head(),
                  "time": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "name": name,
                  "n": n, "m": len(self.edges),
                  "edges": [list(e) for e in self.edges], "cap": cap,
                  "sym_on": bool(sym_on),
                  "extra_units": list(extra_units or []),
                  "check_at": check_at,
                  "gens": [{"vperm": list(g[0]), "eperm": list(g[1])}
                           for g in (gens or [])],
                  "format": "pol=1 forbids all-in-part2 (negative literals); "
                            "edge variable = index+1"}
        self.f.write(json.dumps(header) + "\n")

    def emit(self, tag, pol, kedges, cert):
        """kedges: list of edges (any order/orientation) of the clause;
        cert: certificate over the same vertices. Validates, then writes."""
        ke = [norm_edge(u, v) for u, v in kedges]
        assert cert is not None and certificate_valid(cert, set(ke)), \
            f"INVALID CERTIFICATE ({tag}): {cert} for {ke}"
        idx = [self.eidx[e] for e in ke]  # KeyError => edge not in graph => abort
        self.f.write(json.dumps({"t": tag, "pol": int(pol), "e": idx,
                                 "c": cert}, separators=(",", ":")) + "\n")
        self.count[tag] += 1

    def close(self, verdict, stats=None):
        self.f.write(json.dumps({"type": "footer", "verdict": verdict,
                                 "counts": self.count, "stats": stats,
                                 "time": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
                     + "\n")
        self.f.close()
