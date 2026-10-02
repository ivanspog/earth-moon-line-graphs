import Biplanar.Instances.A4M13S.Base

/-! The 16 cubes of `a4_m13s` (DIMACS: [[33, 53, 16, 37], [33, 53, 16, -37], [33, 53, -16, 37], [33, 53, -16, -37], [33, -53, 16, 37], [33, -53, 16, -37], [33, -53, -16, 37], [33, -53, -16, -37], [-33, 53, 16, 37], [-33, 53, 16, -37], [-33, 53, -16, 37], [-33, 53, -16, -37], [-33, -53, 16, 37], [-33, -53, 16, -37], [-33, -53, -16, 37], [-33, -53, -16, -37]]). -/

namespace Biplanar.A4M13S

def cube1 : LRATCatcher.Cube := [(32, true), (52, true), (15, true), (36, true)]
def cube2 : LRATCatcher.Cube := [(32, true), (52, true), (15, true), (36, false)]
def cube3 : LRATCatcher.Cube := [(32, true), (52, true), (15, false), (36, true)]
def cube4 : LRATCatcher.Cube := [(32, true), (52, true), (15, false), (36, false)]
def cube5 : LRATCatcher.Cube := [(32, true), (52, false), (15, true), (36, true)]
def cube6 : LRATCatcher.Cube := [(32, true), (52, false), (15, true), (36, false)]
def cube7 : LRATCatcher.Cube := [(32, true), (52, false), (15, false), (36, true)]
def cube8 : LRATCatcher.Cube := [(32, true), (52, false), (15, false), (36, false)]
def cube9 : LRATCatcher.Cube := [(32, false), (52, true), (15, true), (36, true)]
def cube10 : LRATCatcher.Cube := [(32, false), (52, true), (15, true), (36, false)]
def cube11 : LRATCatcher.Cube := [(32, false), (52, true), (15, false), (36, true)]
def cube12 : LRATCatcher.Cube := [(32, false), (52, true), (15, false), (36, false)]
def cube13 : LRATCatcher.Cube := [(32, false), (52, false), (15, true), (36, true)]
def cube14 : LRATCatcher.Cube := [(32, false), (52, false), (15, true), (36, false)]
def cube15 : LRATCatcher.Cube := [(32, false), (52, false), (15, false), (36, true)]
def cube16 : LRATCatcher.Cube := [(32, false), (52, false), (15, false), (36, false)]

def cubes : List LRATCatcher.Cube := [cube1, cube2, cube3, cube4, cube5, cube6, cube7, cube8, cube9, cube10, cube11, cube12, cube13, cube14, cube15, cube16]

end Biplanar.A4M13S
