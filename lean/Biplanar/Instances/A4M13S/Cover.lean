import Biplanar.Instances.A4M13S.Cubes

/-! Cover completeness for `a4_m13s`: the negated-cubes formula is UNSAT
    (`data/a4_m13s/cover.lrat`), so every assignment satisfies some cube. -/

namespace Biplanar.A4M13S

lrat_reflect_cnf cover_unsat (LRATCatcher.negCubesCNF Biplanar.A4M13S.cubes) "data/a4_m13s/cover.lrat"

end Biplanar.A4M13S
