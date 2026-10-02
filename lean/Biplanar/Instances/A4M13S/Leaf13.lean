import Biplanar.Instances.A4M13S.W13
import Biplanar.Instances.A4M13S.Cubes
import Biplanar.Sym

/-! Leaf 13 of 16: cube `[-33, -53, 16, 37]` (DIMACS), refuted by
    `data/a4_m13s/leaf13.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m13s_13 data/a4_m13s/leaf13.cnf -33 -53 16 37`). -/

namespace Biplanar.A4M13S

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf13_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M13S.cube13 Biplanar.A4M13S.F13) "data/a4_m13s/leaf13.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 13. -/
theorem leaf13 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube13.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws13 gens cube13 (by native_decide)
    (by native_decide) (by native_decide) leaf13_unsat planar H2

end Biplanar.A4M13S
