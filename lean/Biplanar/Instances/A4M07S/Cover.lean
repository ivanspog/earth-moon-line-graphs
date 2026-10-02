import Biplanar.Instances.A4M07S.Cubes

/-! Cover completeness for `a4_m07s`: the negated-cubes formula is UNSAT
    (`data/a4_m07s/cover.lrat`), so every assignment satisfies some cube. -/

namespace Biplanar.A4M07S

lrat_reflect_cnf cover_unsat (LRATCatcher.negCubesCNF Biplanar.A4M07S.cubes) "data/a4_m07s/cover.lrat"

end Biplanar.A4M07S
