import Biplanar.Instances.A4M04C.W7
import Biplanar.Instances.A4M04C.Cubes
import Biplanar.Sym

/-! Leaf 7 of 22: cube `[-105, -94, 136, -143, -106, 145, 146]` (DIMACS), refuted by
    `data/a4_m04c/leaf7.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m04c_7 data/a4_m04c/leaf7.cnf -105 -94 136 -143 -106 145 146`). -/

namespace Biplanar.A4M04C

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf7_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M04C.cube7 Biplanar.A4M04C.F7) "data/a4_m04c/leaf7.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 7. -/
theorem leaf7 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube7.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws7 gens cube7 (by native_decide)
    (by native_decide) (by native_decide) leaf7_unsat planar H2

end Biplanar.A4M04C
