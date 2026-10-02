import Biplanar.Instances.A4M06.Defs
import Biplanar.Sym

/-! Certified non-biplanarity of `a4_m06` (A4 member 06 of F-034: the line graph L(M) of the 7-vertex multigraph M with multiplicities [05:2 06:6 14:5 15:3 23:5 24:1 25:1 26:1 34:1 35:2 46:1] (n = 28); P-008 A(ii) rests on its non-biplanarity) from a
    SYMMETRY-BROKEN formula: `F` carries the lex clauses of 17
    automorphism generators, proved sound in `Biplanar/Sym.lean`, so the
    theorem needs the third elementary hypothesis (H3) — planarity is an
    isomorphism invariant. Certificate `data/a4_m06/F.lrat` refutes the
    DIMACS file written by
    `lake exe biplanar-export a4_m06 data/a4_m06/F.cnf`. -/

namespace Biplanar.A4M06

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf F_unsat (Biplanar.A4M06.F) "data/a4_m06/F.lrat"

/-- **Conditional non-biplanarity theorem (Stage 2, counter-free).** For
    every predicate `planar` on edge lists satisfying the elementary
    direction of Kuratowski's theorem (H2) and isomorphism invariance (H3),
    the graph `G` admits no partition of its edges into two `planar` parts.
    Euler's bound is not needed. -/
theorem not_biplanar (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S)
    (H3 : Biplanar.IsoInvariant G planar) :
    ¬ Biplanar.Biplanar planar G :=
  Biplanar.not_biplanar_of_unsat_sym₀ G ws gens (by native_decide) (by native_decide)
    (by native_decide) F_unsat planar H2 H3

#print axioms not_biplanar

end Biplanar.A4M06
