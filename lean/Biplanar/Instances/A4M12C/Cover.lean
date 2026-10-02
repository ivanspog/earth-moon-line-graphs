import Biplanar.Instances.A4M12C.Cubes

/-! Cover completeness for `a4_m12c`: the negated-cubes formula is UNSAT
    (`data/a4_m12c/cover.lrat`), so every assignment satisfies some cube. -/

namespace Biplanar.A4M12C

lrat_reflect_cnf cover_unsat (LRATCatcher.negCubesCNF Biplanar.A4M12C.cubes) "data/a4_m12c/cover.lrat"

end Biplanar.A4M12C
