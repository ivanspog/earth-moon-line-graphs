import Biplanar.Instances.A4M12C.W11
import Biplanar.Instances.A4M12C.Cubes
import Biplanar.Sym

/-! Leaf 11 of 18: cube `[105, -53, -95, -149]` (DIMACS), refuted by
    `data/a4_m12c/leaf11.lrat` (CaDiCaL on the DIMACS file written by
    `lake exe biplanar-export a4_m12c_11 data/a4_m12c/leaf11.cnf 105 -53 -95 -149`). -/

namespace Biplanar.A4M12C

-- `native_decide` reflection is cheap at run time, but a declaration's
-- checks share one elaboration budget and the default trips on large
-- witness lists. Raising it changes no axiom.
set_option maxHeartbeats 2000000

lrat_reflect_cnf leaf11_unsat
  (LRATCatcher.Cube.leafCNF Biplanar.A4M12C.cube11 Biplanar.A4M12C.F11) "data/a4_m12c/leaf11.lrat"

/-- No lex-minimal biplanar partition of `G` agrees with cube 11. -/
theorem leaf11 (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ Biplanar.lexOK G gens σ = true ∧
        cube11.sat (Biplanar.valSym G gens G.edges.length σ) = true ∧
        planar (Biplanar.part G σ false) ∧ planar (Biplanar.part G σ true) :=
  Biplanar.not_biplanar_on_cube_of_unsat_sym₀ G ws11 gens cube11 (by native_decide)
    (by native_decide) (by native_decide) leaf11_unsat planar H2

end Biplanar.A4M12C
