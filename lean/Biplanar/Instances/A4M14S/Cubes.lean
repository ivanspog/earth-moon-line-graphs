import Biplanar.Instances.A4M14S.Base

/-! The 4 cubes of `a4_m14s` (DIMACS: [[17, 42], [17, -42], [-17, 42], [-17, -42]]). -/

namespace Biplanar.A4M14S

def cube1 : LRATCatcher.Cube := [(16, true), (41, true)]
def cube2 : LRATCatcher.Cube := [(16, true), (41, false)]
def cube3 : LRATCatcher.Cube := [(16, false), (41, true)]
def cube4 : LRATCatcher.Cube := [(16, false), (41, false)]

def cubes : List LRATCatcher.Cube := [cube1, cube2, cube3, cube4]

end Biplanar.A4M14S
