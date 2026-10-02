import Biplanar.Instances.A4M14S.W3
import Biplanar.Instances.A4M14S.Cubes
import Biplanar.Sym

/-! Leaf 3 of 4: cube `[-17, 42]` (DIMACS), refuted by
    `data/a4_m14s/leaf3.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m14s_3 data/a4_m14s/leaf3.cnf -17 42`). -/

namespace Biplanar.A4M14S

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf3_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M14S.cube3 Biplanar.A4M14S.F3) "data/a4_m14s/leaf3.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 3. -/
theorem leaf3 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube3.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws3 gens cube3 (by native_decide)
    (by native_decide) (by native_decide) leaf3_unsat planar H2

end Biplanar.A4M14S
