import Biplanar.Instances.A4M11C.Base

/-! The 18 cubes of `a4_m11c` (DIMACS: [[-107, -128, -146, -60], [-107, -128, -146, 60], [-107, -128, 146, -60, -94], [-107, -128, 146, -60, 94], [-107, -128, 146, 60], [-107, 128, -146, -60, -108], [-107, 128, -146, -60, 108], [-107, 128, -146, 60], [-107, 128, 146, -60], [-107, 128, 146, 60], [107, -128, -146, -60], [107, -128, -146, 60], [107, -128, 146, -60], [107, -128, 146, 60], [107, 128, -146, -60], [107, 128, -146, 60], [107, 128, 146, -60], [107, 128, 146, 60]]). -/

namespace Biplanar.A4M11C

def cube1 : LRATCatcher.Cube := [(106, false), (127, false), (145, false), (59, false)]
def cube2 : LRATCatcher.Cube := [(106, false), (127, false), (145, false), (59, true)]
def cube3 : LRATCatcher.Cube := [(106, false), (127, false), (145, true), (59, false), (93, false)]
def cube4 : LRATCatcher.Cube := [(106, false), (127, false), (145, true), (59, false), (93, true)]
def cube5 : LRATCatcher.Cube := [(106, false), (127, false), (145, true), (59, true)]
def cube6 : LRATCatcher.Cube := [(106, false), (127, true), (145, false), (59, false), (107, false)]
def cube7 : LRATCatcher.Cube := [(106, false), (127, true), (145, false), (59, false), (107, true)]
def cube8 : LRATCatcher.Cube := [(106, false), (127, true), (145, false), (59, true)]
def cube9 : LRATCatcher.Cube := [(106, false), (127, true), (145, true), (59, false)]
def cube10 : LRATCatcher.Cube := [(106, false), (127, true), (145, true), (59, true)]
def cube11 : LRATCatcher.Cube := [(106, true), (127, false), (145, false), (59, false)]
def cube12 : LRATCatcher.Cube := [(106, true), (127, false), (145, false), (59, true)]
def cube13 : LRATCatcher.Cube := [(106, true), (127, false), (145, true), (59, false)]
def cube14 : LRATCatcher.Cube := [(106, true), (127, false), (145, true), (59, true)]
def cube15 : LRATCatcher.Cube := [(106, true), (127, true), (145, false), (59, false)]
def cube16 : LRATCatcher.Cube := [(106, true), (127, true), (145, false), (59, true)]
def cube17 : LRATCatcher.Cube := [(106, true), (127, true), (145, true), (59, false)]
def cube18 : LRATCatcher.Cube := [(106, true), (127, true), (145, true), (59, true)]

def cubes : List LRATCatcher.Cube := [cube1, cube2, cube3, cube4, cube5, cube6, cube7, cube8, cube9, cube10, cube11, cube12, cube13, cube14, cube15, cube16, cube17, cube18]

end Biplanar.A4M11C
