import Biplanar.Instances.A4M01.Defs
import Biplanar.Sym

/-! Certified non-biplanarity of `a4_m01` (A4 member 01 of F-034: the line graph L(M) of the 7-vertex multigraph M with multiplicities [05:2 06:6 14:4 15:2 16:2 23:5 25:3 34:3 45:1] (n = 28); P-008 A(ii) rests on its non-biplanarity) from a
    SYMMETRY-BROKEN formula: `F` carries the lex clauses of 19
    automorphism generators, proved sound in `Biplanar/Sym.lean`, so the
    theorem needs the third elementary hypothesis (H3) — planarity is an
    isomorphism invariant. Certificate `data/a4_m01/F.lrat` refutes the
    DIMACS file written by
    `lake exe biplanar-export a4_m01 data/a4_m01/F.cnf`. -/

namespace Biplanar.A4M01

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf F_unsat (Biplanar.A4M01.F) "data/a4_m01/F.lrat"

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

end Biplanar.A4M01
