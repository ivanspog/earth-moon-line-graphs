import Biplanar.Instances.A4M14S.Cubes

/-! Cover completeness for `a4_m14s`: the negated-cubes formula is UNSAT
    (`data/a4_m14s/cover.lrat`), so every assignment satisfies some cube. -/

namespace Biplanar.A4M14S

lrat_reflect_cnf cover_unsat (LRATCatcher.negCubesCNF Biplanar.A4M14S.cubes) "data/a4_m14s/cover.lrat"

end Biplanar.A4M14S
