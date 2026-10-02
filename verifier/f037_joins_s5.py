#!/usr/bin/env python3
"""F-037 Lemma J (s >= 5): the finite fact used in the proof that K_s v H biplanar
(s >= 5, H arbitrary) implies chi_f <= 9.  Checks, exactly, over the complete graph atlas
(all graphs on <= 7 vertices):  omega <= 3  =>  chi_f <= 4,   and   omega <= 2 => chi_f <= 3
(the s = 6 case needs only n <= 6, triangle-free, min degree >= 3)."""
import networkx as nx
from f037_common import chi_f, omega, relabel

worst3 = worst2 = 0
cnt = 0
for G in nx.graph_atlas_g()[1:]:
    G = relabel(G)
    if G.number_of_edges() == 0:
        continue
    w = omega(G)
    if w <= 3:
        cnt += 1
        lo, hi, _ = chi_f(G)
        assert lo == hi
        worst3 = max(worst3, hi) if w <= 3 else worst3
        if w <= 2:
            worst2 = max(worst2, hi)
print(f"atlas graphs with omega<=3: {cnt};  max chi_f (omega<=3) = {worst3};  max chi_f (omega<=2) = {worst2}")
assert worst3 <= 4 and worst2 <= 3
print("Lemma J finite fact: OK")
