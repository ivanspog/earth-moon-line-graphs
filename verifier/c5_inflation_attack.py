"""Stage-2 attack: biplanarity of the two unexamined n=19 C5-inflations.

F-007 shows the alpha=2 route reduces to exactly three C5-inflations on 19
vertices; KSS 2023 killed C5[3,4,4,4,4]. The two live candidates, both
chi >= 10 (alpha = 2) with 98 edges vs ceiling 102:

    C5[3,3,5,3,5]   and   C5[3,4,4,3,5]

A partition for either SOLVES the FrontierMath problem. Failure proves
nothing (NP-hard). Random-restart greedy + repair, one seed per restart,
progress logged.

Usage: .venv/bin/python verifier/c5_inflation_attack.py --seeds 0 100000
"""
from __future__ import annotations

import itertools
import json
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from biplanar_search import find_biplanar_partition  # noqa: E402

CANDS = ([3, 3, 5, 3, 5], [3, 4, 4, 3, 5])


def inflate_c5(w):
    n = sum(w)
    bags, s = [], 0
    for x in w:
        bags.append(list(range(s, s + x)))
        s += x
    edges = []
    for b in bags:
        edges += list(itertools.combinations(b, 2))
    for i in range(5):
        edges += [(u, v) for u in bags[i] for v in bags[(i + 1) % 5]]
    return n, sorted(tuple(sorted(e)) for e in edges)


def main() -> None:
    lo, hi = (int(sys.argv[sys.argv.index("--seeds") + 1]),
              int(sys.argv[sys.argv.index("--seeds") + 2]))
    graphs = [(w, *inflate_c5(w)) for w in CANDS]
    for w, n, edges in graphs:
        print(f"C5{w}: n={n} m={len(edges)}", flush=True)
    for seed in range(lo, hi):
        for w, n, edges in graphs:
            part = find_biplanar_partition(n, edges, seed=seed, restarts=1,
                                           repair_rounds=5000)
            if part:
                tag = "_".join(map(str, w))
                path = os.path.join(os.path.dirname(__file__), "..",
                                    "population", f"c5_{tag}_partition.json")
                with open(path, "w") as f:
                    json.dump({"num_vertices": n,
                               "edges_part1": [list(e) for e in part[0]],
                               "edges_part2": [list(e) for e in part[1]],
                               "weights": w, "seed": seed}, f)
                print(f"*** PARTITION FOUND for C5{w} at seed {seed} -> {path} ***",
                      flush=True)
                return
        if seed % 25 == 0:
            print(f"seed {seed}: nothing", flush=True)


if __name__ == "__main__":
    main()
