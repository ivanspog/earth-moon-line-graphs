"""Explicit Kuratowski-subdivision certificates (Lean-verification milestone, P1).

A *certificate* makes "these edges contain a subdivision of K5 or K3,3"
checkable by a definition a reader can audit in one screen, with no graph
algorithm in the trusted base:

    {"kind": "K5" | "K33",
     "branch": [b_0, ..., b_4]            # K5: 5 branch vertices
              | [a_0, a_1, a_2, b_0, b_1, b_2],   # K33: side A then side B
     "paths":  [p_0, p_1, ...]}           # one vertex sequence per branch pair

Branch pairs are enumerated in a FIXED order (K5: (b_i, b_j) for i < j in
lexicographic order, 10 pairs; K33: (a_i, b_j) for i in 0..2, j in 0..2,
9 pairs) and `paths[k]` must run from the first to the second vertex of the
k-th pair. A certificate is VALID for an edge set E iff

  * the branch vertices are pairwise distinct (5 for K5, 6 for K33);
  * there are exactly 10 (K5) or 9 (K33) paths, path k has >= 2 vertices,
    starts/ends at the k-th pair, and has no repeated vertex;
  * every consecutive pair of a path is an edge of E (unordered);
  * no internal path vertex is a branch vertex, and internal vertices of
    different paths are pairwise distinct.

That is verbatim the definition of "E contains a subdivision of K5/K3,3"
(branch vertices + internally disjoint connecting paths), so the elementary
direction of Kuratowski's theorem gives: valid certificate => E non-planar.
`certificate_valid` below is the reference implementation;
`lean/Biplanar/Basic.lean::KurCert.valid` mirrors it line by line (the
Lean side is what the machine-checked theorem trusts; this file only has to
agree with it on every certificate we emit, which `lean_static_resolve.py`
re-checks before anything reaches Lean).

`extract_certificate` turns the Kuratowski subgraph returned by
`networkx.check_planarity(..., counterexample=True)` (an edge list) into a
certificate; any irregularity returns None (the caller must REJECT — this
module never accepts anything it did not fully verify).
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations


def norm_edge(u, v):
    return (u, v) if u <= v else (v, u)


def branch_pairs(kind, branch):
    if kind == "K5":
        assert len(branch) == 5
        return [(branch[i], branch[j]) for i, j in combinations(range(5), 2)]
    if kind == "K33":
        assert len(branch) == 6
        return [(branch[i], branch[3 + j]) for i in range(3) for j in range(3)]
    raise ValueError(kind)


def certificate_valid(cert, edge_set):
    """Reference validity check (see module docstring). `edge_set` is a set
    of unordered edges given as sorted pairs. Pure Python, no networkx."""
    try:
        kind, branch, paths = cert["kind"], list(cert["branch"]), list(cert["paths"])
    except (KeyError, TypeError):
        return False
    if kind == "K5":
        if len(branch) != 5:
            return False
    elif kind == "K33":
        if len(branch) != 6:
            return False
    else:
        return False
    if len(set(branch)) != len(branch):
        return False
    pairs = branch_pairs(kind, branch)
    if len(paths) != len(pairs):
        return False
    bset = set(branch)
    internal_all = []
    for (s, t), p in zip(pairs, paths):
        p = list(p)
        if len(p) < 2 or p[0] != s or p[-1] != t:
            return False
        if len(set(p)) != len(p):
            return False
        for u, v in zip(p, p[1:]):
            if norm_edge(u, v) not in edge_set:
                return False
        inner = p[1:-1]
        if any(v in bset for v in inner):
            return False
        internal_all.extend(inner)
    if len(set(internal_all)) != len(internal_all):
        return False
    return True


def extract_certificate(kedges):
    """Build a certificate from the edge list of a Kuratowski subgraph (a
    subdivision of K5 or K3,3). Returns None on any irregularity."""
    adj = defaultdict(set)
    for u, v in kedges:
        if u == v:
            return None
        adj[u].add(v)
        adj[v].add(u)
    branch = sorted(v for v in adj if len(adj[v]) >= 3)
    if len(branch) == 5:
        kind = "K5"
        if any(len(adj[v]) != 4 for v in branch):
            return None
    elif len(branch) == 6:
        kind = "K33"
        if any(len(adj[v]) != 3 for v in branch):
            return None
    else:
        return None
    if any(len(adj[v]) != 2 for v in adj if v not in branch):
        return None
    bset = set(branch)
    paths = {}
    for b in branch:
        for w in adj[b]:
            prev, cur = b, w
            path = [b, w]
            while cur not in bset:
                nbrs = adj[cur] - {prev}
                if len(nbrs) != 1:
                    return None
                nxt = next(iter(nbrs))
                path.append(nxt)
                prev, cur = cur, nxt
            if cur == b:
                return None
            key = (b, cur)
            if (cur, b) in paths:
                continue  # same path, seen from the other end
            if key in paths:
                return None  # two paths between one branch pair: not a subdivision
            paths[key] = path
    if kind == "K5":
        branch_out = branch
    else:
        a0 = branch[0]
        side_b = sorted(t for (s, t) in paths if s == a0) + \
            sorted(s for (s, t) in paths if t == a0)
        side_b = sorted(set(side_b))
        side_a = sorted(bset - set(side_b))
        if len(side_a) != 3 or len(side_b) != 3 or a0 not in side_a:
            return None
        branch_out = side_a + side_b
    ordered = []
    for s, t in branch_pairs(kind, branch_out):
        if (s, t) in paths:
            ordered.append(paths[(s, t)])
        elif (t, s) in paths:
            ordered.append(list(reversed(paths[(t, s)])))
        else:
            return None
    cert = {"kind": kind, "branch": branch_out, "paths": ordered}
    edge_set = {norm_edge(u, v) for u, v in kedges}
    if not certificate_valid(cert, edge_set):
        return None
    # every edge of the subgraph must be used by some path (K is exactly the
    # subdivision); not needed for soundness, but catches extraction bugs
    used = {norm_edge(u, v) for p in ordered for u, v in zip(p, p[1:])}
    if used != edge_set:
        return None
    return cert


def clique_certificate(vertices):
    """Certificate for a K5 on 5 vertices (all paths are single edges)."""
    b = sorted(vertices)
    return {"kind": "K5", "branch": b,
            "paths": [[s, t] for s, t in branch_pairs("K5", b)]}


def k33_certificate(side_a, side_b):
    """Certificate for a K3,3 with the given sides (all paths single edges)."""
    b = sorted(side_a) + sorted(side_b)
    return {"kind": "K33", "branch": b,
            "paths": [[s, t] for s, t in branch_pairs("K33", b)]}


def cert_to_lean_line(pol, edge_indices, cert):
    """Compact integer line consumed by lean/Biplanar/Basic.lean::parseWitnesses:
       pol nE e_1..e_nE kind nB b_1..b_nB nP (len v_1..v_len)*
    kind: 5 = K5, 33 = K33. pol = 1: 'not all these edges in part 2'
    (negative literals); pol = 0: 'not all in part 1' (positive literals)."""
    kind = 5 if cert["kind"] == "K5" else 33
    toks = [pol, len(edge_indices), *edge_indices, kind, len(cert["branch"]),
            *cert["branch"], len(cert["paths"])]
    for p in cert["paths"]:
        toks.append(len(p))
        toks.extend(p)
    return " ".join(map(str, toks))


def _selftest():
    import random
    import networkx as nx
    rng = random.Random(7)
    ok = 0
    for trial in range(300):
        base = nx.complete_graph(5) if trial % 2 == 0 else \
            nx.complete_bipartite_graph(3, 3)
        g = nx.Graph()
        nxt = base.number_of_nodes()
        relabel = {v: v + rng.randrange(0, 3) * 0 for v in base}  # identity
        for u, v in base.edges():
            k = rng.randrange(0, 4)
            prev = relabel[u]
            for _ in range(k):
                g.add_edge(prev, nxt)
                prev, nxt = nxt, nxt + 1
            g.add_edge(prev, relabel[v])
        # random vertex relabeling
        perm = list(g.nodes())
        rng.shuffle(perm)
        mp = dict(zip(g.nodes(), perm))
        kedges = [norm_edge(mp[u], mp[v]) for u, v in g.edges()]
        cert = extract_certificate(kedges)
        assert cert is not None, kedges
        assert certificate_valid(cert, set(kedges))
        # tampering must be rejected
        bad = dict(cert)
        bad["paths"] = [list(p) for p in cert["paths"]]
        bad["paths"][0] = bad["paths"][0][:-1] + [10 ** 6]
        assert not certificate_valid(bad, set(kedges))
        missing = set(kedges) - {kedges[0]}
        assert not certificate_valid(cert, missing)
        ok += 1
    # a prism (non-subdivision, all degrees 3) must be rejected
    prism = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]
    assert extract_certificate(prism) is None
    # K3,3 sides must be reconstructed correctly under relabeling
    c = extract_certificate([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
                             (2, 3), (2, 4), (2, 5)])
    assert c["branch"] == [0, 1, 2, 3, 4, 5], c
    print(f"kuratowski_cert selftest OK ({ok} random subdivisions)")


if __name__ == "__main__":
    _selftest()
