#!/usr/bin/env python3
"""F-035: targeted extension of the one boundary sub-case P-007 leaves open,
s = 0, d = 11, omega(H) = 6, chi_f(H) = 9 exactly (so 9 | m and m even: 18 | m).

For each m given, every 11-regular circulant C_m(D) (all labelled D = +-S with m/2 in
S, no multiplier reduction, so nothing can be lost to a canonicalisation bug) is tested:
omega(H) = 6 first (cheap: a clique search inside N(0); P-007's vertex-transitive Reed
bound forces omega >= 6 for chi_f = 9, and omega >= 7 is covered by P-007's Kneser
cases), then alpha(H) <= m/9 (an independent set of size m/9 + 1 through vertex 0 kills).
Prints every hit; the expected output is none.

Run: .venv/bin/python -u verifier/f035_boundary_d11.py 90 108 126 144
"""
import itertools
import sys
import time
from math import gcd

from f035_circulant_family import adj_bits, alpha_at_least, conn_set, omega_vt

for m in map(int, sys.argv[1:]):
    t0 = time.time()
    tested = om6 = hits = 0
    pool = range(1, m // 2)
    for T in itertools.combinations(pool, 5):
        S = T + (m // 2,)
        g = m
        for x in S:
            g = gcd(g, x)
        if g != 1:
            continue
        tested += 1
        D = conn_set(m, S)
        adj = adj_bits(m, D)
        if omega_vt(m, adj) != 6:
            continue
        om6 += 1
        if alpha_at_least(m, adj, m // 9 + 1):
            continue
        hits += 1
        print(f"HIT m={m} S={S}", flush=True)
    print(f"m={m}: {tested} connected labelled 11-regular circulants, {om6} with omega=6, "
          f"{hits} with chi_f >= 9  [{time.time() - t0:.0f}s]", flush=True)
