import Biplanar.Instances.A4M11C.Cubes

/-! Cover completeness for `a4_m11c`: the negated-cubes formula is UNSAT
    (`data/a4_m11c/cover.lrat`), so every assignment satisfies some cube. -/

namespace Biplanar.A4M11C

lrat_reflect_cnf cover_unsat (LRATCatcher.negCubesCNF Biplanar.A4M11C.cubes) "data/a4_m11c/cover.lrat"

end Biplanar.A4M11C
