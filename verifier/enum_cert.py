"""Certificates for the Lean check of the two root enumerations of P-008 (line graphs).

UNTRUSTED proposer: Lean (`lean/Biplanar/Enum/*.lean`) re-checks everything it uses. This script
  * lists the isomorphism classes of the root multigraphs Lean will meet:
      - 5 vertices: Delta <= 8, every triple sum <= 8, 19 or 20 edges (157 classes, F5);
      - 7 vertices: 8-regular, every triple sum <= 8, sum_p C(m_p, 2) >= 40 (73 classes, F32);
  * for each class representative r, finds a certificate on the line graph L(r):
      - ('euler', W): a vertex set W of L(r), |W| >= 3, with e(L(r)[W]) > 6|W| - 12;
      - ('tf', W, T): T a triangle-free set of edges of L(r)[W] with |T| > 4|W| - 8 (RC2 MaxSAT);
      - ('iso', i, pi): L(r) is isomorphic to the i-th A4 graph (the graph of the certified Lean
        theorem A4M<i>), pi[v] = image of vertex v (networkx VF2);
  * writes `lean/Biplanar/Enum/Data.lean`.

Vertex order of L(r) (must match `Biplanar.Enum.lineGraph`): root edges in pair order
(0,1),(0,2),...,(k-2,k-1), each pair repeated by its multiplicity; L-edges (x, y) with x < y.

Usage: .venv/bin/python verifier/enum_cert.py
"""
import itertools
import json
import os
import re
import sys

import networkx as nx
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
A4 = ['00', '01', '02', '03', '04C', '05', '06', '07S', '08', '09C', '10', '11C', '12C', '13S',
      '14', '15', '16', '17', '18', '19', '20', '21']


def pairs(k):
    return [(i, j) for i in range(k) for j in range(i + 1, k)]


def root_edges(k, a):
    return [p for p, m in zip(pairs(k), a) for _ in range(m)]


def meets(p, q):
    return p[0] == q[0] or p[0] == q[1] or p[1] == q[0] or p[1] == q[1]


def line_edges(k, a):
    R = root_edges(k, a)
    return [(x, y) for x in range(len(R)) for y in range(x + 1, len(R)) if meets(R[x], R[y])]


def canon(k, a):
    P = pairs(k)
    idx = {p: t for t, p in enumerate(P)}
    best = None
    for s in itertools.permutations(range(k)):
        v = [0] * len(P)
        for t, (i, j) in enumerate(P):
            u, w = sorted((s[i], s[j]))
            v[idx[(u, w)]] = a[t]
        v = tuple(v)
        if best is None or v < best:
            best = v
    return best


def enum5():
    """all 5-vertex vectors with Delta <= 8, triple sums <= 8, 19 or 20 edges, up to iso."""
    P = pairs(5)
    idx = {p: t for t, p in enumerate(P)}
    seen, out = set(), []
    a = [0] * 10

    def ok(t):
        deg = [0] * 5
        for s in range(t + 1):
            deg[P[s][0]] += a[s]
            deg[P[s][1]] += a[s]
        if max(deg) > 8:
            return False
        for u, v, w in itertools.combinations(range(5), 3):
            if max(idx[(u, v)], idx[(u, w)], idx[(v, w)]) <= t and \
                    a[idx[(u, v)]] + a[idx[(u, w)]] + a[idx[(v, w)]] > 8:
                return False
        return True

    def rec(t):
        if t == 10:
            if sum(a) in (19, 20):
                c = canon(5, a)
                if c not in seen:
                    seen.add(c)
                    out.append(list(c))
            return
        for x in range(9):
            a[t] = x
            if ok(t):
                rec(t + 1)
        a[t] = 0
    rec(0)
    return out


def euler_witness(k, a, E):
    """vertex sets of L induced by root vertex subsets U."""
    R = root_edges(k, a)
    Es = set(E)
    for size in range(k, 1, -1):
        for U in itertools.combinations(range(k), size):
            W = [x for x, p in enumerate(R) if p[0] in U and p[1] in U]
            if len(W) < 3:
                continue
            Ws = set(W)
            e = sum(1 for (x, y) in E if x in Ws and y in Ws)
            if e > 6 * len(W) - 12:
                return ('euler', W)
    return None


def tf_witness(k, a, E):
    R = root_edges(k, a)
    for size in range(k, 1, -1):
        for U in itertools.combinations(range(k), size):
            W = [x for x, p in enumerate(R) if p[0] in U and p[1] in U]
            if len(W) < 3:
                continue
            Ws = set(W)
            EW = [e for e in E if e[0] in Ws and e[1] in Ws]
            if len(EW) <= 4 * len(W) - 8:
                continue
            ix = {e: i + 1 for i, e in enumerate(EW)}
            adj = {}
            for x, y in EW:
                adj.setdefault(x, set()).add(y)
                adj.setdefault(y, set()).add(x)
            w = WCNF()
            for x, y in EW:
                for z in adj[x] & adj[y]:
                    if z > y:
                        w.append([-ix[(x, y)], -ix[(x, z)], -ix[(y, z)]])
            for e in EW:
                w.append([ix[e]], weight=1)
            with RC2(w) as rc2:
                m = rc2.compute()
            Tset = [EW[i - 1] for i in m if 0 < i <= len(EW)]
            if len(Tset) > 4 * len(W) - 8:
                G = nx.Graph(Tset)
                assert sum(nx.triangles(G).values()) == 0
                return ('tf', W, sorted(Tset))
    return None


def load_a4():
    gs = []
    for m in A4:
        sub = 'Base' if m[-1] in 'SC' else 'Defs'  # split / per-cube instances keep G in Base.lean
        txt = open(os.path.join(ROOT, f'lean/Biplanar/Instances/A4M{m}/{sub}.lean')).read()
        mm = re.search(r'def G : Biplanar\.Graph := ⟨(\d+), \[([^\]]*)\]⟩', txt)
        n = int(mm.group(1))
        E = [tuple(map(int, x)) for x in re.findall(r'\((\d+), (\d+)\)', mm.group(2))]
        gs.append((m, n, E))
    return gs


def certify(k, reps, a4=None):
    out = []
    for r in reps:
        E = line_edges(k, r)
        c = euler_witness(k, r, E) or tf_witness(k, r, E)
        if c is None and a4 is not None:
            L = nx.Graph(E)
            L.add_nodes_from(range(len(root_edges(k, r))))
            for i, (m, n, EG) in enumerate(a4):
                G = nx.Graph(EG)
                G.add_nodes_from(range(n))
                gm = nx.isomorphism.GraphMatcher(L, G)
                if gm.is_isomorphic():
                    pi = [gm.mapping[v] for v in range(n)]
                    assert {tuple(sorted((pi[x], pi[y]))) for x, y in E} == set(EG)
                    c = ('iso', i, pi)
                    break
        if c is None:
            raise SystemExit(f'no certificate for {k}-vertex class {r}')
        out.append(c)
    return out


def lean_list(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def lean_edges(es):
    return '[' + ', '.join(f'({x}, {y})' for x, y in es) + ']'


def lean_cert(c):
    if c[0] == 'euler':
        return f'.euler {lean_list(c[1])}'
    if c[0] == 'tf':
        return f'.tf {lean_list(c[1])} {lean_edges(c[2])}'
    return f'.iso {c[1]} {lean_list(c[2])}'


def main():
    reps7 = json.load(open(os.path.join(ROOT, 'verifier/f032_classes.json')))
    a4 = load_a4()
    reps5 = enum5()
    print('classes: 5-vertex', len(reps5), '7-vertex', len(reps7), flush=True)
    c5 = certify(5, reps5)
    c7 = certify(7, reps7, a4)
    kinds = lambda cs: {k: sum(1 for c in cs if c[0] == k) for k in ('euler', 'tf', 'iso')}
    print('5-vertex certificates', kinds(c5), '7-vertex certificates', kinds(c7), flush=True)
    isos = sorted(c[1] for c in c7 if c[0] == 'iso')
    assert isos == list(range(22)), isos
    lines = ['import Biplanar.Enum.Defs', '',
             '/-! Generated by `verifier/enum_cert.py`: class representatives, their certificates and the',
             '    22 A4 graphs (edge lists copied verbatim from `Instances/A4M*/Defs.lean`). Untrusted data:',
             '    every certificate is re-checked by `Biplanar.Enum.check5` / `check7`. -/', '',
             'namespace Biplanar.Enum', '']
    lines.append('def reps5 : List (List Nat) := [')
    lines.append(',\n'.join('  ' + lean_list(r) for r in reps5) + ']')
    lines.append('def certs5 : List Cert := [')
    lines.append(',\n'.join('  ' + lean_cert(c) for c in c5) + ']')
    lines.append('def reps7 : List (List Nat) := [')
    lines.append(',\n'.join('  ' + lean_list(r) for r in reps7) + ']')
    lines.append('def certs7 : List Cert := [')
    lines.append(',\n'.join('  ' + lean_cert(c) for c in c7) + ']')
    lines.append('/-- The 22 graphs of the certified theorems `Biplanar.A4M<i>.not_biplanar`, in the order')
    lines.append(f'    {", ".join(A4)}. -/')
    lines.append('def a4Graphs : List Graph := [')
    lines.append(',\n'.join(f'  ⟨{n}, {lean_edges(E)}⟩' for m, n, E in a4) + ']')
    lines += ['', 'end Biplanar.Enum', '']
    path = os.path.join(ROOT, 'lean/Biplanar/Enum/Data.lean')
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w').write('\n'.join(lines))
    print('wrote', path, os.path.getsize(path), 'bytes')


if __name__ == '__main__':
    main()
