import Biplanar.Instances.A4M14S.W2
import Biplanar.Instances.A4M14S.Cubes
import Biplanar.Sym

/-! Leaf 2 of 4: cube `[17, -42]` (DIMACS), refuted by
    `data/a4_m14s/leaf2.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m14s_2 data/a4_m14s/leaf2.cnf 17 -42`). -/

namespace Biplanar.A4M14S

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf2_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M14S.cube2 Biplanar.A4M14S.F2) "data/a4_m14s/leaf2.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 2. -/
theorem leaf2 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube2.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws2 gens cube2 (by native_decide)
    (by native_decide) (by native_decide) leaf2_unsat planar H2

end Biplanar.A4M14S
