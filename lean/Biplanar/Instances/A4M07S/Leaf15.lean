import Biplanar.Instances.A4M07S.W15
import Biplanar.Instances.A4M07S.Cubes
import Biplanar.Sym

/-! Leaf 15 of 16: cube `[-53, -151, -73, 86]` (DIMACS), refuted by
    `data/a4_m07s/leaf15.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m07s_15 data/a4_m07s/leaf15.cnf -53 -151 -73 86`). -/

namespace Biplanar.A4M07S

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf15_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M07S.cube15 Biplanar.A4M07S.F15) "data/a4_m07s/leaf15.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 15. -/
theorem leaf15 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube15.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws15 gens cube15 (by native_decide)
    (by native_decide) (by native_decide) leaf15_unsat planar H2

end Biplanar.A4M07S
