#!/usr/bin/env python3
"""F-038: the Lean statement is about the right graph.

For each certified A4 member, parse `G` and the multiplicity string out of
lean/Biplanar/Instances/A4M<i>/Defs.lean and check, on a code path independent
of f034_a4_line_graph_sat.build(), that G is isomorphic to the line graph of
the multigraph M (networkx line_graph of a MultiGraph).

Usage: .venv/bin/python verifier/f038_lean_graph_check.py 1 2 3
       .venv/bin/python verifier/f038_lean_graph_check.py --file lean/Biplanar/Instances/A4M17S/Base.lean
(a split-route instance keeps G in Base.lean; its doc line carries the multiplicities)
"""
import os
import re
import sys

import networkx as nx

ROOT = __file__.rsplit("/verifier/", 1)[0]
bad = 0
args = sys.argv[1:]
files = ([(os.path.basename(os.path.dirname(args[1])), args[1])] if args[:1] == ["--file"]
         else [(f"A4M{int(x):02d}", f"{ROOT}/lean/Biplanar/Instances/A4M{int(x):02d}/Defs.lean")
               for x in args])
for label, path in files:
    src = open(path).read()
    mults = re.search(r"multiplicities \[([^\]]*)\]", src).group(1)
    n, body = re.search(r"def G : Biplanar.Graph := ⟨(\d+), \[(.*?)\]⟩", src, re.S).groups()
    E = [tuple(map(int, t)) for t in re.findall(r"\((\d+), (\d+)\)", body)]
    G = nx.Graph()
    G.add_nodes_from(range(int(n)))
    G.add_edges_from(E)
    M = nx.MultiGraph()
    for tok in mults.split():
        uv, k = tok.split(":")
        M.add_edges_from([(int(uv[0]), int(uv[1]))] * int(k))
    L = nx.Graph(nx.line_graph(M))
    ok = len(E) == len(set(E)) and all(u < v for u, v in E) and nx.is_isomorphic(G, L)
    bad += not ok
    print(f"{label}: G n={G.number_of_nodes()} e={len(E)} | L(M) n={L.number_of_nodes()} "
          f"e={L.number_of_edges()} | {'OK' if ok else 'MISMATCH'} | [{mults}]")
sys.exit(1 if bad else 0)
