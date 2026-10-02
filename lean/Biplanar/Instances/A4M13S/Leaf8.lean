import Biplanar.Instances.A4M13S.W8
import Biplanar.Instances.A4M13S.Cubes
import Biplanar.Sym

/-! Leaf 8 of 16: cube `[33, -53, -16, -37]` (DIMACS), refuted by
    `data/a4_m13s/leaf8.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m13s_8 data/a4_m13s/leaf8.cnf 33 -53 -16 -37`). -/

namespace Biplanar.A4M13S

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf8_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M13S.cube8 Biplanar.A4M13S.F8) "data/a4_m13s/leaf8.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 8. -/
theorem leaf8 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube8.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws8 gens cube8 (by native_decide)
    (by native_decide) (by native_decide) leaf8_unsat planar H2

end Biplanar.A4M13S
