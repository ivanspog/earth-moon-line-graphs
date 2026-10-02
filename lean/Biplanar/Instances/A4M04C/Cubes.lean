import Biplanar.Instances.A4M04C.Base

/-! The 22 cubes of `a4_m04c` (DIMACS: [[-105, -94, -136, -143, -106, -145], [-105, -94, -136, -143, -106, 145], [-105, -94, -136, -143, 106], [-105, -94, -136, 143], [-105, -94, 136, -143, -106, -145], [-105, -94, 136, -143, -106, 145, -146], [-105, -94, 136, -143, -106, 145, 146], [-105, -94, 136, -143, 106], [-105, -94, 136, 143], [-105, 94, -136, -143], [-105, 94, -136, 143, -145], [-105, 94, -136, 143, 145], [-105, 94, 136, -143], [-105, 94, 136, 143], [105, -94, -136, -143], [105, -94, -136, 143], [105, -94, 136, -143], [105, -94, 136, 143], [105, 94, -136, -143], [105, 94, -136, 143], [105, 94, 136, -143], [105, 94, 136, 143]]). -/

namespace Biplanar.A4M04C

def cube1 : LRATCatcher.Cube := [(104, false), (93, false), (135, false), (142, false), (105, false), (144, false)]
def cube2 : LRATCatcher.Cube := [(104, false), (93, false), (135, false), (142, false), (105, false), (144, true)]
def cube3 : LRATCatcher.Cube := [(104, false), (93, false), (135, false), (142, false), (105, true)]
def cube4 : LRATCatcher.Cube := [(104, false), (93, false), (135, false), (142, true)]
def cube5 : LRATCatcher.Cube := [(104, false), (93, false), (135, true), (142, false), (105, false), (144, false)]
def cube6 : LRATCatcher.Cube := [(104, false), (93, false), (135, true), (142, false), (105, false), (144, true), (145, false)]
def cube7 : LRATCatcher.Cube := [(104, false), (93, false), (135, true), (142, false), (105, false), (144, true), (145, true)]
def cube8 : LRATCatcher.Cube := [(104, false), (93, false), (135, true), (142, false), (105, true)]
def cube9 : LRATCatcher.Cube := [(104, false), (93, false), (135, true), (142, true)]
def cube10 : LRATCatcher.Cube := [(104, false), (93, true), (135, false), (142, false)]
def cube11 : LRATCatcher.Cube := [(104, false), (93, true), (135, false), (142, true), (144, false)]
def cube12 : LRATCatcher.Cube := [(104, false), (93, true), (135, false), (142, true), (144, true)]
def cube13 : LRATCatcher.Cube := [(104, false), (93, true), (135, true), (142, false)]
def cube14 : LRATCatcher.Cube := [(104, false), (93, true), (135, true), (142, true)]
def cube15 : LRATCatcher.Cube := [(104, true), (93, false), (135, false), (142, false)]
def cube16 : LRATCatcher.Cube := [(104, true), (93, false), (135, false), (142, true)]
def cube17 : LRATCatcher.Cube := [(104, true), (93, false), (135, true), (142, false)]
def cube18 : LRATCatcher.Cube := [(104, true), (93, false), (135, true), (142, true)]
def cube19 : LRATCatcher.Cube := [(104, true), (93, true), (135, false), (142, false)]
def cube20 : LRATCatcher.Cube := [(104, true), (93, true), (135, false), (142, true)]
def cube21 : LRATCatcher.Cube := [(104, true), (93, true), (135, true), (142, false)]
def cube22 : LRATCatcher.Cube := [(104, true), (93, true), (135, true), (142, true)]

def cubes : List LRATCatcher.Cube := [cube1, cube2, cube3, cube4, cube5, cube6, cube7, cube8, cube9, cube10, cube11, cube12, cube13, cube14, cube15, cube16, cube17, cube18, cube19, cube20, cube21, cube22]

end Biplanar.A4M04C
