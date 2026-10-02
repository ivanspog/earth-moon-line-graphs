"""Search for a biplanar partition of a given graph's edge set.

Randomised greedy insertion with swap-repair, deterministic under `seed`.
Not a decision procedure: failure to find a partition proves nothing
(biplanarity testing is NP-hard, Mansfield 1983). Success yields a
certificate checkable in linear time by verify.py.
"""
from __future__ import annotations

import random

import networkx as nx


def _planar_with(G: nx.Graph, e) -> bool:
    G.add_edge(*e)
    ok, _ = nx.check_planarity(G, counterexample=False)
    if not ok:
        G.remove_edge(*e)
    return ok


def find_biplanar_partition(n: int, edges: list[tuple[int, int]], seed: int = 0,
                            restarts: int = 400, repair_rounds: int = 3000):
    """Return (edges1, edges2) or None."""
    rng = random.Random(seed)
    edges = [tuple(sorted(e)) for e in edges]
    for _ in range(restarts):
        order = edges[:]
        rng.shuffle(order)
        G1, G2 = nx.Graph(), nx.Graph()
        G1.add_nodes_from(range(n))
        G2.add_nodes_from(range(n))
        homeless = []
        for e in order:
            first, second = (G1, G2) if rng.random() < 0.5 else (G2, G1)
            if _planar_with(first, e) or _planar_with(second, e):
                continue
            homeless.append(e)
        for _ in range(repair_rounds):
            if not homeless:
                return sorted(G1.edges()), sorted(G2.edges())
            e = homeless.pop(rng.randrange(len(homeless)))
            placed = False
            for G in (G1, G2) if rng.random() < 0.5 else (G2, G1):
                if _planar_with(G, e):
                    placed = True
                    break
            if not placed:
                # evict a random edge from a random side, insert e there if possible
                G = G1 if rng.random() < 0.5 else G2
                if G.number_of_edges():
                    out = list(G.edges())[rng.randrange(G.number_of_edges())]
                    G.remove_edge(*out)
                    if _planar_with(G, e):
                        homeless.append(tuple(sorted(out)))
                    else:
                        G.add_edge(*out)
                        homeless.append(e)
                else:
                    homeless.append(e)
        if not homeless:
            return sorted(G1.edges()), sorted(G2.edges())
    return None
