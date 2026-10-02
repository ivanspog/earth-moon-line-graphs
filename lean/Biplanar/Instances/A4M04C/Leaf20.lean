import Biplanar.Instances.A4M04C.W20
import Biplanar.Instances.A4M04C.Cubes
import Biplanar.Sym

/-! Leaf 20 of 22: cube `[105, 94, -136, 143]` (DIMACS), refuted by
    `data/a4_m04c/leaf20.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m04c_20 data/a4_m04c/leaf20.cnf 105 94 -136 143`). -/

namespace Biplanar.A4M04C

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf20_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M04C.cube20 Biplanar.A4M04C.F20) "data/a4_m04c/leaf20.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 20. -/
theorem leaf20 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube20.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws20 gens cube20 (by native_decide)
    (by native_decide) (by native_decide) leaf20_unsat planar H2

end Biplanar.A4M04C
