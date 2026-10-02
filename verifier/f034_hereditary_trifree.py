#!/usr/bin/env python3
"""F-034 step A1: the HEREDITARY triangle-free count, decided exactly by weighted MaxSAT.

A triangle-free planar graph on s >= 3 vertices has at most 2s - 4 edges, so in a
biplanar graph every triangle-free subgraph T spanning a vertex set S (|S| >= 3)
has |T| <= 4|S| - 8 (Trivedi Q. 7.1 / Szeider 2026 §7 state the |S| = n case).
This script computes max over (S, T) of |T| - 4|S| exactly (RC2 MaxSAT:
soft +1 per edge kept, soft -4 per vertex used, hard: T triangle-free, T inside
G[S], |S| >= 3).  Biplanar requires the maximum to be <= -8; a larger value is
a proof of non-biplanarity with an explicit witness (S, T), re-checked below.

Targets: the palette graph P and the 23 open line graphs of F-033.
Run (detached, ~1 core-hour):
  nohup caffeinate -i .venv/bin/python -u verifier/f034_hereditary_trifree.py \
      > population/f034-hereditary-trifree.log 2>&1 & disown
"""
import itertools
import os
import subprocess
import sys
import time

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f033_fractional_certificates import palette  # noqa: E402


def best_margin(n, E):
    G = nx.Graph(E)
    E = [tuple(sorted(e)) for e in E]
    x = {e: i + 1 for i, e in enumerate(E)}
    y = {v: len(E) + 1 + v for v in range(n)}
    w = WCNF()
    for (u, v), xe in x.items():
        w.append([-xe, y[u]])
        w.append([-xe, y[v]])
    for a, b, c in itertools.combinations(range(n), 3):
        if G.has_edge(a, b) and G.has_edge(a, c) and G.has_edge(b, c):
            w.append([-x[(a, b)], -x[(a, c)], -x[(b, c)]])
    for cl in CardEnc.atleast(list(y.values()), 3, top_id=len(E) + n,
                              encoding=EncType.seqcounter).clauses:
        w.append(cl)
    for xe in x.values():
        w.append([xe], weight=1)
    for yv in y.values():
        w.append([-yv], weight=4)
    with RC2(w) as r:
        model = set(l for l in r.compute() if l > 0)
    T = [e for e in E if x[e] in model]
    S = {v for v in range(n) if y[v] in model}
    # independent re-check of the witness
    assert all(u in S and v in S for u, v in T)
    assert sum(nx.triangles(nx.Graph(T)).values()) == 0 if T else True
    return len(T) - 4 * len(S), len(T), len(S)


def line_graph(mult):
    lab = [e for e, k in sorted(mult.items()) for _ in range(k)]
    E = [(i, j) for i, j in itertools.combinations(range(len(lab)), 2)
         if set(lab[i]) & set(lab[j])]
    return len(lab), E


def targets():
    yield "P (palette)", *palette()
    out = subprocess.run([sys.executable, os.path.join(HERE, "f033_line_graph_route.py")],
                         capture_output=True, text=True, check=True).stdout
    for row in out.split("OPEN:")[1].strip().split("\n")[1:]:
        toks = row.split()
        mult = {(int(t[0]), int(t[1])): int(t.split(":")[1]) for t in toks[1:] if ":" in t}
        yield f"LG {toks[0]} {' '.join(t for t in toks[1:] if ':' in t)}", *line_graph(mult)


if __name__ == "__main__":
    print(f"# f034_hereditary_trifree  pid {os.getpid()}  {time.ctime()}", flush=True)
    dead = 0
    for name, n, E in targets():
        t0 = time.time()
        m, t, s = best_margin(n, E)
        verdict = "DEAD (not biplanar)" if m > -8 else "survives"
        dead += m > -8
        print(f"{name}: n={n} e={len(E)} max(|T|-4|S|)={m} (|T|={t}, |S|={s}) -> {verdict}"
              f"  [{time.time() - t0:.0f}s]", flush=True)
    print(f"# DONE {time.ctime()}: {dead} killed", flush=True)
