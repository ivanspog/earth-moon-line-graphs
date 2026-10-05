#!/usr/bin/env python3
"""F-036 (milestone C-h6, step F3): scored local search for biplanar graphs with large
fractional chromatic number.

SEARCH SPACE.  A state is a pair (T1, T2) of triangulations of the sphere on the vertex set
0..n-1 (each has exactly 3n - 6 edges); the graph is G = T1 u T2.  Nothing is lost by
restricting to triangulations: every planar layer on n >= 3 vertices extends to a
triangulation on the same vertices, and adding edges never lowers chi_f.  So
phi_2 = sup_n max { chi_f(T1 u T2) }, and every state is biplanar BY CONSTRUCTION
(layer 1 = T1, layer 2 = T2 minus T1).

MOVES.  A triangulation is stored as its set of triangles.  (a) diagonal flip in T1 or T2:
the two faces uvw, uvx become wxu, wxv; valid iff wx is not already an edge, which is exactly
when the result is again a triangulated sphere (a bistellar 2-2 move).  (b) hub flip: the
same move, on an edge of the link of a random vertex h, chosen so that h gains a neighbour
(F-035: a chi_f > 9 witness needs vertices with d(v) + omega(v) >= 18).  (c) BGS
permuted-layer move: relabel T2 by a transposition of two vertices.  Default mix 0.3 hub /
0.6 plain / 0.1 relabel.

SCORE.  chi_f(G), computed by column generation: the LP min sum z_I s.t. every vertex covered
>= 1 over a pool of independent sets, priced by an EXACT maximum-weight independent set
(bitset branch-and-bound with a greedy clique-cover bound).  Floating point is used only to
steer the search.  Every state reaching chi_f >= 9 - 1e-9 is re-derived exactly: rational
dual (every maximal independent set checked, via f034_fractional_census) proves the lower
bound, and its fractionally critical CORE (greedy vertex deletion keeping chi_f >= 9) is
extracted, certified, and de-duplicated up to isomorphism.

STOP RULE (owner's standing order).  If a state has an EXACT certified chi_f > 9, the
worker writes population/f036/ALERT with the graph and exits; every worker checks for
ALERT each iteration and exits too.  The follow-up (chi >= 10 by exact SAT colouring,
submission JSON, verifier/verify.py, ATTRIBUTION entry, tell the owner) is done by hand.

Usage:
  f036_fracsearch.py --n 20 --evals 20000 --seed 1 --tag w1 [--start k5c8|corpus|random]
Logs to population/f036/<tag>.log (python -u, one line per report).
"""
from __future__ import annotations

import argparse
import glob
import json
import math
import os
import random
import sys
import time
from fractions import Fraction as Fr

import networkx as nx
import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
OUT = os.path.join(ROOT, "population", "f036")
ALERT = os.path.join(OUT, "ALERT")
EPS = 1e-9


# ---------------------------------------------------------------- triangulations

class Tri:
    """Triangulated sphere on vertices 0..n-1, stored as a face set."""

    def __init__(self, n, faces):
        self.n = n
        self.faces = set()
        self.e2f = {}
        self.adj = [set() for _ in range(n)]
        for f in faces:
            self._add(frozenset(f))

    def _add(self, f):
        self.faces.add(f)
        a, b, c = tuple(f)
        for u, v in ((a, b), (b, c), (a, c)):
            e = frozenset((u, v))
            lst = self.e2f.setdefault(e, [])
            lst.append(f)
            self.adj[u].add(v)
            self.adj[v].add(u)

    def _remove(self, f):
        self.faces.remove(f)
        a, b, c = tuple(f)
        for u, v in ((a, b), (b, c), (a, c)):
            e = frozenset((u, v))
            lst = self.e2f[e]
            lst.remove(f)
            if not lst:
                del self.e2f[e]
                self.adj[u].discard(v)
                self.adj[v].discard(u)

    def edges(self):
        return list(self.e2f)

    def flip(self, e):
        """Flip edge e; returns the new edge, or None if the flip is invalid."""
        f1, f2 = self.e2f[e]
        (w,) = f1 - e
        (x,) = f2 - e
        if x in self.adj[w]:
            return None
        u, v = tuple(e)
        self._remove(f1)
        self._remove(f2)
        self._add(frozenset((w, x, u)))
        self._add(frozenset((w, x, v)))
        return frozenset((w, x))

    def hub_flip(self, h, rng):
        """Flip an edge of the link of h so that h gains a neighbour (F-035's lesson: a
        chi_f > 9 witness needs high-degree hubs).  Returns (old_edge, new_edge) or None."""
        link = []
        for u in self.adj[h]:
            for f in self.e2f[frozenset((h, u))]:
                link.append(f - {h})
        rng.shuffle(link)
        for e in link:
            f1, f2 = self.e2f[e]
            other = f2 if h in f1 else f1
            (x,) = other - e
            if x != h and x not in self.adj[h]:
                new = self.flip(e)
                if new is not None:
                    return e, new
        return None

    def relabelled(self, perm):
        return Tri(self.n, [frozenset(perm[a] for a in f) for f in self.faces])

    def insert(self, f):
        """Insert a new vertex z = n into face f (a 1-3 move)."""
        z = self.n
        self.n += 1
        self.adj.append(set())
        a, b, c = tuple(f)
        self._remove(f)
        for g in ((a, b, z), (b, c, z), (a, c, z)):
            self._add(frozenset(g))
        return z

    def valid(self):
        n = self.n
        ok = len(self.faces) == 2 * n - 4 and len(self.e2f) == 3 * n - 6
        ok = ok and all(len(fs) == 2 for fs in self.e2f.values())
        return ok

    @staticmethod
    def from_planar_edges(n, edges, rng):
        """Complete a planar graph on 0..n-1 to a triangulation, then read its faces."""
        g = nx.Graph()
        g.add_nodes_from(range(n))
        g.add_edges_from(edges)
        assert nx.check_planarity(g)[0]
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not g.has_edge(u, v)]
        rng.shuffle(non)
        for u, v in non:
            if g.number_of_edges() == 3 * n - 6:
                break
            g.add_edge(u, v)
            if not nx.check_planarity(g)[0]:
                g.remove_edge(u, v)
        assert g.number_of_edges() == 3 * n - 6
        ok, emb = nx.check_planarity(g)
        seen, faces = set(), set()
        for u, v in emb.edges():
            if (u, v) in seen:
                continue
            face = emb.traverse_face(u, v, mark_half_edges=seen)
            assert len(face) == 3, face
            faces.add(frozenset(face))
        t = Tri(n, faces)
        assert t.valid()
        return t

    @staticmethod
    def random(n, rng, flips=None):
        """Random stacked triangulation followed by random flips."""
        t = Tri(4, [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)])
        while t.n < n:
            t.insert(rng.choice(sorted(t.faces, key=sorted)))
        for _ in range(flips if flips is not None else 10 * n):
            t.flip(rng.choice(t.edges()))
        return t


# ---------------------------------------------------------------- fractional chromatic number

def bits(x):
    while x:
        low = x & -x
        yield low.bit_length() - 1
        x ^= low


def is_independent(c, adj):
    for v in bits(c):
        if adj[v] & c:
            return False
    return True


def mwis(adj, w, n, need=None):
    """Exact maximum-weight independent set (weights w >= 0, floats).
    Returns (mask, weight).  If `need` is given, stops at the first set heavier than it."""
    order = sorted((v for v in range(n) if w[v] > 1e-12), key=lambda v: -w[v])
    pos_mask = 0
    for v in order:
        pos_mask |= 1 << v
    best = [0, 0.0]

    def bound(cand):
        # greedy clique cover of cand (heaviest first): sum of the heaviest weight per clique
        cliques = []  # list of [mask, maxw]
        total = 0.0
        for v in order:
            if not (cand >> v) & 1:
                continue
            for cl in cliques:
                if cl[0] & ~adj[v] == 0:
                    cl[0] |= 1 << v
                    break
            else:
                cliques.append([1 << v, w[v]])
                total += w[v]
        return total

    def rec(cand, cur, curw):
        if curw > best[1]:
            best[0], best[1] = cur, curw
            if need is not None and curw > need:
                return True
        if not cand:
            return False
        if curw + bound(cand) <= best[1] + 1e-12:
            return False
        for v in order:
            if not (cand >> v) & 1:
                continue
            cand &= ~(1 << v)
            if rec(cand & ~adj[v], cur | (1 << v), curw + w[v]):
                return True
            if curw + bound(cand) <= best[1] + 1e-12:
                return False
        return False

    rec(pos_mask, 0, 0.0)
    return best[0], best[1]


def greedy_is(adj, w, n, rng=None):
    order = sorted(range(n), key=lambda v: -w[v])
    c, cw, forb = 0, 0.0, 0
    for v in order:
        if not (forb >> v) & 1:
            c |= 1 << v
            cw += w[v]
            forb |= adj[v] | (1 << v)
    return c, cw


class ChiF:
    """Column-generation chi_f with a warm pool of independent sets."""

    def __init__(self, n, cap=600):
        self.n = n
        self.cap = cap
        self.pool = []

    def value(self, adj):
        n = self.n
        pool = [c for c in self.pool if is_independent(c, adj)]
        have = set(pool)
        for v in range(n):
            if (1 << v) not in have:
                pool.append(1 << v)
        for _ in range(500):
            A = np.zeros((n, len(pool)))
            for j, c in enumerate(pool):
                for v in bits(c):
                    A[v, j] = 1.0
            res = linprog(np.ones(len(pool)), A_ub=-A, b_ub=-np.ones(n), bounds=(0, None),
                          method="highs")
            y = [max(0.0, -m) for m in res.ineqlin.marginals]
            c, cw = greedy_is(adj, y, n)
            if cw <= 1 + 1e-9:
                c, cw = mwis(adj, y, n, need=1 + 1e-9)
            if cw <= 1 + 1e-9:
                break
            pool.append(c)
        else:
            raise RuntimeError("column generation did not converge")
        # keep the support plus the most recent columns
        keep = [c for c, z in zip(pool, res.x) if z > 1e-12]
        rest = [c for c, z in zip(pool, res.x) if z <= 1e-12 and c.bit_count() > 1]
        self.pool = keep + rest[-max(0, self.cap - len(keep)):]
        return res.fun, y


# ---------------------------------------------------------------- state

class State:
    def __init__(self, t1, t2):
        assert t1.n == t2.n
        self.t1, self.t2 = t1, t2
        self.n = t1.n

    def adj_bits(self):
        adj = []
        for v in range(self.n):
            b = 0
            for u in self.t1.adj[v] | self.t2.adj[v]:
                b |= 1 << u
            adj.append(b)
        return adj

    def union_edges(self):
        return sorted(tuple(sorted(e)) for e in set(self.t1.e2f) | set(self.t2.e2f))

    def layers(self):
        e1 = sorted(tuple(sorted(e)) for e in self.t1.e2f)
        s1 = set(e1)
        e2 = sorted(tuple(sorted(e)) for e in self.t2.e2f if tuple(sorted(e)) not in s1)
        return e1, e2

    def copy(self):
        return State(Tri(self.n, self.t1.faces), Tri(self.n, self.t2.faces))

    def grow_to(self, n, rng):
        while self.n < n:
            self.t1.insert(rng.choice(sorted(self.t1.faces, key=sorted)))
            self.t2.insert(rng.choice(sorted(self.t2.faces, key=sorted)))
            self.n += 1


def load_partition(path, rng):
    obj = json.load(open(path))
    n = obj["num_vertices"]
    e1 = [tuple(e) for e in obj["edges_part1"]]
    e2 = [tuple(e) for e in obj["edges_part2"]]
    return State(Tri.from_planar_edges(n, e1, rng), Tri.from_planar_edges(n, e2, rng))


def load_corpus_pair(l0, l1, rng):
    def rd(p):
        E = set()
        for line in open(p):
            t = line.split()
            if len(t) >= 2 and t[0].lstrip("-").isdigit():
                u, v = int(t[0]), int(t[1])
                if u != v:
                    E.add((min(u, v), max(u, v)))
        return E
    E0, E1 = rd(l0), rd(l1)
    V = sorted({x for e in E0 | E1 for x in e})
    lab = {v: i for i, v in enumerate(V)}  # contiguous labels (no label gaps)
    n = len(V)
    E0 = [(lab[u], lab[v]) for u, v in E0]
    E1 = [(lab[u], lab[v]) for u, v in E1]
    return State(Tri.from_planar_edges(n, E0, rng), Tri.from_planar_edges(n, E1, rng))


def corpus_pairs(corpus):
    out = []
    for l0 in sorted(glob.glob(os.path.join(corpus, "**", "*_layer0.edges"), recursive=True)):
        l1 = l0.replace("_layer0.edges", "_layer1.edges")
        if os.path.exists(l1):
            out.append((l0, l1))
    return out


# ---------------------------------------------------------------- exact certification + cores

def certify(n, E):
    """Exact chi_f interval [lo, hi] by the f034 census routine (all maximal independent
    sets, LP, rational dual and primal re-checked with fractions)."""
    from f034_fractional_census import chi_f as census_chi_f
    assert sorted({x for e in E for x in e}) == list(range(n)), "label gaps"
    lo, hi, alpha, nmis = census_chi_f(n, E)
    return lo, hi, alpha, nmis


def core(n, E, target, rng):
    """Greedy vertex deletion keeping float chi_f >= target - EPS.  Returns (n', E')."""
    V = list(range(n))
    Eset = set(E)
    order = sorted(V, key=lambda v: sum(1 for e in Eset if v in e))
    alive = set(V)
    for v in order:
        trial = alive - {v}
        idx = {u: i for i, u in enumerate(sorted(trial))}
        E2 = [(idx[a], idx[b]) for a, b in Eset if a in trial and b in trial]
        adj = [0] * len(trial)
        for a, b in E2:
            adj[a] |= 1 << b
            adj[b] |= 1 << a
        val, _ = ChiF(len(trial)).value(adj)
        if val >= target - 1e-7:
            alive = trial
    idx = {u: i for i, u in enumerate(sorted(alive))}
    E2 = sorted((min(idx[a], idx[b]), max(idx[a], idx[b])) for a, b in Eset
                if a in alive and b in alive)
    return len(alive), E2, sorted(alive)


def planar_both(n, e1, e2):
    import planarity
    for part in (e1, e2):
        g = nx.Graph()
        g.add_nodes_from(range(n))
        g.add_edges_from(part)
        if not nx.check_planarity(g)[0]:
            return False
        if part and not planarity.is_planar([tuple(e) for e in part]):
            return False
    return True


# ---------------------------------------------------------------- search

def search(args):
    rng = random.Random(args.seed)
    os.makedirs(os.path.join(OUT, "records"), exist_ok=True)
    log = open(os.path.join(OUT, f"{args.tag}.log"), "a", buffering=1)

    def say(msg):
        log.write(f"{time.strftime('%H:%M:%S')} {msg}\n")

    say(f"# f036 worker {args.tag} pid {os.getpid()} n={args.n} evals={args.evals} "
        f"seed={args.seed} start={args.start}")
    corpus = corpus_pairs(args.corpus) if args.corpus else []
    import re
    corpus = [p for p in corpus
              if int(re.search(r"_(\d+)v_", os.path.basename(p[0])).group(1)) <= args.n]
    say(f"corpus pairs usable at n <= {args.n}: {len(corpus)}")

    def fresh():
        kind = args.start
        if kind == "mix":
            kind = rng.choice(["k5c8", "corpus", "random"] if corpus else ["k5c8", "random"])
        if kind == "k5c8":
            st = load_partition(os.path.join(ROOT, "population", "satprop_f034-K5vC8sq_partition.json"), rng)
        elif kind == "corpus":
            l0, l1 = rng.choice(corpus)
            st = load_corpus_pair(l0, l1, rng)
        else:
            st = State(Tri.random(args.n, rng), Tri.random(args.n, rng))
        st.grow_to(args.n, rng)
        return st, kind

    st, kind = fresh()
    eng = ChiF(st.n)
    cur, _ = eng.value(st.adj_bits())
    best = cur
    say(f"start {kind}: chi_f={cur:.6f}")
    hist = {}
    seen_cores = {}  # wl-hash -> list of (n, E)
    n_cores = 0
    ev = 0
    t0 = time.time()
    last = t0
    steps_since_improve = 0
    T0, T1 = args.temp, args.temp / 20
    stage_len = args.stage

    if args.mode == "ils":
        return ils(args, rng, fresh, say, seen_cores)

    while ev < args.evals:
        if os.path.exists(ALERT):
            say("ALERT file present: another worker found chi_f > 9; exiting")
            return
        # temperature: geometric within a stage, then restart
        frac = (steps_since_improve % stage_len) / stage_len
        T = T0 * (T1 / T0) ** frac
        r = rng.random()
        undo = None
        if r < args.hub:  # hub flip: a random vertex gains a neighbour in a random layer
            t = st.t1 if rng.random() < 0.5 else st.t2
            hf = t.hub_flip(rng.randrange(st.n), rng)
            if hf is None:
                continue
            undo = ("flip", t, hf[1])
        elif r < 0.9:  # diagonal flip in a random layer
            t = st.t1 if rng.random() < 0.5 else st.t2
            e = rng.choice(t.edges())
            new = t.flip(e)
            if new is None:
                continue
            undo = ("flip", t, new)
        else:
            i, j = rng.sample(range(st.n), 2)
            perm = list(range(st.n))
            perm[i], perm[j] = j, i
            old = st.t2
            st.t2 = old.relabelled(perm)
            undo = ("perm", old, None)
        val, _ = eng.value(st.adj_bits())
        ev += 1
        key = round(val * 60) / 60
        hist[key] = hist.get(key, 0) + 1
        d = val - cur
        if d >= -1e-12 or rng.random() < math.exp(d / max(T, 1e-9)):
            cur = val
        else:
            if undo[0] == "flip":
                assert undo[1].flip(undo[2]) is not None
            else:
                st.t2 = undo[1]
            continue
        if cur > best + 1e-9:
            best = cur
            steps_since_improve = 0
            say(f"ev {ev}: new best chi_f={best:.6f}")
        else:
            steps_since_improve += 1
        if cur >= 9 - 1e-7 and (cur > 9 + 1e-6 or ev - handle_record.last_ev >= args.core_every):
            handle_record.last_ev = ev
            handle_record(st, cur, args, rng, seen_cores, say)
            n_cores = sum(len(v) for v in seen_cores.values())
        if steps_since_improve and steps_since_improve % (stage_len * args.restart_stages) == 0:
            st, kind = fresh()
            eng = ChiF(st.n)
            cur, _ = eng.value(st.adj_bits())
            say(f"ev {ev}: restart from {kind}: chi_f={cur:.6f}")
        if time.time() - last > args.report:
            last = time.time()
            top = sorted(hist.items(), reverse=True)[:4]
            say(f"ev {ev} [{ev / (last - t0):.1f}/s] cur={cur:.4f} best={best:.4f} T={T:.4f} "
                f"cores>=9: {n_cores}  top visited: " + ", ".join(f"{k:.4f}x{c}" for k, c in top))
    top = sorted(hist.items(), reverse=True)[:8]
    say(f"# DONE ev={ev} best={best:.6f} cores>=9={n_cores} "
        f"elapsed={time.time() - t0:.0f}s  top visited: " + ", ".join(f"{k:.4f}x{c}" for k, c in top))


def propose(st, args, rng):
    """Apply one random move in place; return an undo record, or None if the move was void."""
    r = rng.random()
    if r < args.hub:
        t = st.t1 if rng.random() < 0.5 else st.t2
        hf = t.hub_flip(rng.randrange(st.n), rng)
        return None if hf is None else ("flip", t, hf[1])
    if r < 0.9:
        t = st.t1 if rng.random() < 0.5 else st.t2
        new = t.flip(rng.choice(t.edges()))
        return None if new is None else ("flip", t, new)
    i, j = rng.sample(range(st.n), 2)
    perm = list(range(st.n))
    perm[i], perm[j] = j, i
    old = st.t2
    st.t2 = old.relabelled(perm)
    return ("perm", old, None)


def revert(st, undo):
    if undo[0] == "flip":
        assert undo[1].flip(undo[2]) is not None
    else:
        st.t2 = undo[1]


def ils(args, rng, fresh, say, seen_cores):
    """Iterated local search on the lexicographic score (chi_f, e(G)).
    Local phase: accept a move iff chi_f does not drop (ties: accept if e(G) does not drop,
    else with prob 0.3, so the walk can cross plateaus).  Stuck (no chi_f gain for
    args.patience evaluations): kick = args.kick random unevaluated moves from the ELITE
    state.  After args.kicks_per_seed kicks without a new elite, restart from a fresh seed."""
    ev = 0
    t0 = last = time.time()
    hist = {}
    best_overall = -1.0
    n_restarts = 0
    while ev < args.evals:
        st, kind = fresh()
        eng = ChiF(st.n)
        cur, _ = eng.value(st.adj_bits())
        cur_e = len(st.union_edges())
        elite, elite_val = st.copy(), cur
        if cur > best_overall + 1e-9:
            best_overall = cur
        n_restarts += 1
        say(f"ev {ev}: seed #{n_restarts} from {kind}: chi_f={cur:.6f}")
        kicks_wo = 0
        stall = 0
        while ev < args.evals and kicks_wo < args.kicks_per_seed:
            if os.path.exists(ALERT):
                say("ALERT file present: another worker found chi_f > 9; exiting")
                return
            undo = propose(st, args, rng)
            if undo is None:
                continue
            val, _ = eng.value(st.adj_bits())
            ev += 1
            key = round(val * 60) / 60
            hist[key] = hist.get(key, 0) + 1
            e_new = len(st.union_edges())
            if val > cur + 1e-9:
                accept, stall = True, 0
            elif val > cur - 1e-9:
                accept = e_new >= cur_e or rng.random() < 0.3
                stall += 1
            else:
                accept = False
                stall += 1
            if accept:
                cur, cur_e = val, e_new
            else:
                revert(st, undo)
            if cur > elite_val + 1e-9:
                elite, elite_val, kicks_wo = st.copy(), cur, 0
                if cur > best_overall + 1e-9:
                    best_overall = cur
                    say(f"ev {ev}: new best chi_f={cur:.6f} (n={st.n}, e={cur_e})")
            if cur >= 9 - 1e-7 and (cur > 9 + 1e-6 or ev - handle_record.last_ev >= args.core_every):
                handle_record.last_ev = ev
                handle_record(st, cur, args, rng, seen_cores, say)
            if stall >= args.patience:
                # kick from the elite state
                st = elite.copy()
                for _ in range(args.kick):
                    propose(st, args, rng)
                eng = ChiF(st.n)
                cur, _ = eng.value(st.adj_bits())
                cur_e = len(st.union_edges())
                ev += 1
                stall = 0
                kicks_wo += 1
            if time.time() - last > args.report:
                last = time.time()
                n_cores = sum(len(v) for v in seen_cores.values())
                top = sorted(hist.items(), reverse=True)[:4]
                say(f"ev {ev} [{ev / (last - t0):.1f}/s] cur={cur:.4f} elite={elite_val:.4f} "
                    f"best={best_overall:.4f} seeds={n_restarts} cores>=9: {n_cores}  top visited: "
                    + ", ".join(f"{k:.4f}x{c}" for k, c in top))
    n_cores = sum(len(v) for v in seen_cores.values())
    top = sorted(hist.items(), reverse=True)[:8]
    say(f"# DONE ev={ev} best={best_overall:.6f} seeds={n_restarts} cores>=9={n_cores} "
        f"elapsed={time.time() - t0:.0f}s  top visited: " + ", ".join(f"{k:.4f}x{c}" for k, c in top))


def handle_record(st, val, args, rng, seen_cores, say):
    """A state with float chi_f >= 9.  If the float says > 9, certify the WHOLE state exactly
    first (the exact rational lower bound decides the ALERT).  Then extract its core
    (chi_f >= 9 kept), certify the core exactly, de-duplicate up to isomorphism."""
    n = st.n
    E = st.union_edges()
    key_state = nx.weisfeiler_lehman_graph_hash(nx.Graph(E))
    if key_state in handle_record.seen_states:
        return
    handle_record.seen_states.add(key_state)
    e1, e2 = st.layers()
    assert planar_both(n, e1, e2), "layer not planar: bug"
    if val > 9 + 1e-6:
        lo, hi, alpha, nmis = certify(n, E)
        say(f"float chi_f={val:.6f} > 9: exact certificate on the full state gives [{lo}, {hi}]")
        if lo is not None and lo > 9:
            # STOP EVERYTHING: exact certified chi_f > 9
            rec = dict(num_vertices=n, edges_part1=[list(e) for e in e1],
                       edges_part2=[list(e) for e in e2], chi_f_lower=str(lo),
                       chi_f_upper=str(hi), alpha=alpha, tag=args.tag)
            path = os.path.join(OUT, "records", f"ALERT-{args.tag}-{int(time.time())}.json")
            json.dump(rec, open(path, "w"))
            with open(ALERT, "w") as f:
                f.write(f"{time.ctime()} {args.tag}: exact chi_f >= {lo} > 9 on n={n}; state {path}\n")
            say(f"!!! ALERT: exact chi_f >= {lo} > 9 (n={n}); wrote {path}; stopping")
            sys.exit(3)
    cn, cE, keepv = core(n, E, 9.0, rng)
    lo, hi, alpha, nmis = certify(cn, cE)
    g = nx.Graph(cE)
    h = nx.weisfeiler_lehman_graph_hash(g)
    for (m, F) in seen_cores.get(h, []):
        if m == cn and nx.is_isomorphic(g, nx.Graph(F)):
            return
    seen_cores.setdefault(h, []).append((cn, cE))
    cid = f"{args.tag}-c{sum(len(v) for v in seen_cores.values()):03d}"
    rec = dict(num_vertices=n, edges_part1=[list(e) for e in e1], edges_part2=[list(e) for e in e2],
               chi_f_float=val, core_n=cn, core_edges=[list(e) for e in cE],
               core_vertices=keepv, core_chi_f=[str(lo), str(hi)], core_alpha=alpha,
               core_wl=h, tag=args.tag)
    json.dump(rec, open(os.path.join(OUT, "records", f"{cid}.json"), "w"))
    say(f"NEW CORE {cid}: state n={n} e={len(E)} chi_f={val:.6f}; core n={cn} e={len(cE)} "
        f"alpha={alpha} chi_f in [{lo}, {hi}] wl={h[:10]}")


handle_record.seen_states = set()
handle_record.last_ev = -10**9


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--evals", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--tag", required=True)
    ap.add_argument("--start", default="mix", choices=["mix", "k5c8", "corpus", "random"])
    ap.add_argument("--corpus", default=os.environ.get("F036_CORPUS", ""))
    ap.add_argument("--temp", type=float, default=0.15)
    ap.add_argument("--stage", type=int, default=400)
    ap.add_argument("--restart-stages", type=int, default=5)
    ap.add_argument("--report", type=float, default=60.0)
    ap.add_argument("--mode", default="ils", choices=["ils", "sa"])
    ap.add_argument("--patience", type=int, default=300)
    ap.add_argument("--kick", type=int, default=3)
    ap.add_argument("--kicks-per-seed", type=int, default=15)
    ap.add_argument("--hub", type=float, default=0.3,
                    help="probability of a hub flip (the rest: 0.9 - hub plain flips, 0.1 relabels)")
    ap.add_argument("--core-every", type=int, default=200,
                    help="at most one core extraction per this many evaluations on the 9-plateau "
                         "(a state with float chi_f > 9 is always handled at once)")
    search(ap.parse_args())
