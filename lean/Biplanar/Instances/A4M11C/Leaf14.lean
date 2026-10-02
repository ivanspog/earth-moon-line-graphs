import Biplanar.Instances.A4M11C.W14
import Biplanar.Instances.A4M11C.Cubes
import Biplanar.Sym

/-! Leaf 14 of 18: cube `[107, -128, 146, 60]` (DIMACS), refuted by
    `data/a4_m11c/leaf14.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m11c_14 data/a4_m11c/leaf14.cnf 107 -128 146 60`). -/

namespace Biplanar.A4M11C

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf14_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M11C.cube14 Biplanar.A4M11C.F14) "data/a4_m11c/leaf14.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 14. -/
theorem leaf14 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube14.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws14 gens cube14 (by native_decide)
    (by native_decide) (by native_decide) leaf14_unsat planar H2

end Biplanar.A4M11C
