#!/usr/bin/env python3
"""F-037: run every lemma of P-008-draft-f5-own against the frozen F5 calibration set.
Per graph: exact chi_f (rational primal+dual certificates), omega, Delta, delta, degeneracy,
mad (exact), and the bounds
   localReed  = max_v (d(v)+1+omega(v))/2            [EK2012 Thm 2]   (must be >= chi_f)
   superlocal = max_uv (d(u)+d(v)+w(u)+w(v)+2)/4     [EK2012 Thm 3]   (must be >= chi_f)
   DR  = (k+1+omega)/2   k = degeneracy               [REFUTED in general, F-037]
   AR  = (mad+1+omega)/2                              [CONJECTURED, F-037]
   L4(T=9) = 9 + chi_f(G[H_9]),  H_9 = {v: d(v)+omega(v)+1 > 18}   (must be >= chi_f)
 and L1 (extension lemma) at every vertex: chi_f(G) <= max(chi_f(G-v), d(v)+1)."""
import sys
from fractions import Fraction as Fr
import networkx as nx
from f037_common import chi_f, degeneracy, omega, relabel
from f037_calib import calibration, mad


def omega_v(G, v):
    return 1 + omega(G.subgraph(list(G[v]))) if G.degree(v) else 1


def main(do_L1=True, include_b=True):
    for tag, G in calibration(include_b):
        lo, hi, _ = chi_f(G)
        assert lo == hi, (tag, lo, hi)
        cf = lo
        w = omega(G); deg = dict(G.degree())
        ov = {v: omega_v(G, v) for v in G}
        lr = max(Fr(deg[v] + 1 + ov[v], 2) for v in G)
        sl = max(Fr(deg[u] + deg[v] + ov[u] + ov[v] + 2, 4) for u, v in G.edges())
        k = degeneracy(G); m = mad(G)
        dr, ar = Fr(k + 1 + w, 2), (m + 1 + w) / 2
        H9 = [v for v in G if deg[v] + ov[v] + 1 > 18]
        l4 = 9 + (chi_f(relabel(G.subgraph(H9)))[1] if H9 else 0)
        l1 = "skip"
        if do_L1:
            bad = []
            for v in G:
                c2 = chi_f(relabel(G.subgraph([u for u in G if u != v])))[1]
                if not cf <= max(c2, deg[v] + 1):
                    bad.append(v)
            l1 = "ok" if not bad else f"FAIL at {bad}"
        flags = []
        if lr < cf or sl < cf or l4 < cf: flags.append("THEOREM-VIOLATION?!")
        if dr < cf: flags.append("DR-violated")
        if ar < cf: flags.append("AR-VIOLATED")
        print(f"{tag[:60]:60s} n={G.number_of_nodes():2d} chi_f={str(cf):6s} w={w} D={max(deg.values())} "
              f"d={min(deg.values())} k={k} mad={str(m):7s} | LR={float(lr):5.2f} SL={float(sl):5.2f} "
              f"DR={float(dr):5.2f} AR={float(ar):5.2f} L4={float(l4):5.2f} |H9|={len(H9)} L1={l1} {' '.join(flags)}",
              flush=True)


if __name__ == "__main__":
    main(do_L1="--no-L1" not in sys.argv, include_b="--no-b" not in sys.argv)
