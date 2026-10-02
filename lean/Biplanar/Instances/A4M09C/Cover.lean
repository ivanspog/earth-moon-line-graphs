import Biplanar.Instances.A4M09C.Cubes

/-! Cover completeness for `a4_m09c`: the negated-cubes formula is UNSAT
    (`data/a4_m09c/cover.lrat`), so every assignment satisfies some cube. -/

namespace Biplanar.A4M09C

lrat_reflect_cnf cover_unsat (LRATCatcher.negCubesCNF Biplanar.A4M09C.cubes) "data/a4_m09c/cover.lrat"

end Biplanar.A4M09C
