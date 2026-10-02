import Biplanar.Instances.A4M04C.W1
import Biplanar.Instances.A4M04C.Cubes
import Biplanar.Sym

/-! Leaf 1 of 22: cube `[-105, -94, -136, -143, -106, -145]` (DIMACS), refuted by
    `data/a4_m04c/leaf1.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m04c_1 data/a4_m04c/leaf1.cnf -105 -94 -136 -143 -106 -145`). -/

namespace Biplanar.A4M04C

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf1_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M04C.cube1 Biplanar.A4M04C.F1) "data/a4_m04c/leaf1.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 1. -/
theorem leaf1 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube1.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws1 gens cube1 (by native_decide)
    (by native_decide) (by native_decide) leaf1_unsat planar H2

end Biplanar.A4M04C
