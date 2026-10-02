import Biplanar.Instances.A4M09C.W18
import Biplanar.Instances.A4M09C.Cubes
import Biplanar.Sym

/-! Leaf 18 of 18: cube `[101, 106, 108, 141]` (DIMACS), refuted by
    `data/a4_m09c/leaf18.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m09c_18 data/a4_m09c/leaf18.cnf 101 106 108 141`). -/

namespace Biplanar.A4M09C

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf18_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M09C.cube18 Biplanar.A4M09C.F18) "data/a4_m09c/leaf18.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 18. -/
theorem leaf18 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube18.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws18 gens cube18 (by native_decide)
    (by native_decide) (by native_decide) leaf18_unsat planar H2

end Biplanar.A4M09C
