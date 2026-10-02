import Biplanar.Instances.A4M04C.Cubes

/-! Cover completeness for `a4_m04c`: the negated-cubes formula is UNSAT
    (`data/a4_m04c/cover.lrat`), so every assignment satisfies some cube. -/

namespace Biplanar.A4M04C

lrat_reflect_cnf cover_unsat (LRATCatcher.negCubesCNF Biplanar.A4M04C.cubes) "data/a4_m04c/cover.lrat"

end Biplanar.A4M04C
