import Biplanar.Instances.A4M07S.Base

/-! The 16 cubes of `a4_m07s` (DIMACS: [[53, 151, 73, 86], [53, 151, 73, -86], [53, 151, -73, 86], [53, 151, -73, -86], [53, -151, 73, 86], [53, -151, 73, -86], [53, -151, -73, 86], [53, -151, -73, -86], [-53, 151, 73, 86], [-53, 151, 73, -86], [-53, 151, -73, 86], [-53, 151, -73, -86], [-53, -151, 73, 86], [-53, -151, 73, -86], [-53, -151, -73, 86], [-53, -151, -73, -86]]). -/

namespace Biplanar.A4M07S

def cube1 : LRATCatcher.Cube := [(52, true), (150, true), (72, true), (85, true)]
def cube2 : LRATCatcher.Cube := [(52, true), (150, true), (72, true), (85, false)]
def cube3 : LRATCatcher.Cube := [(52, true), (150, true), (72, false), (85, true)]
def cube4 : LRATCatcher.Cube := [(52, true), (150, true), (72, false), (85, false)]
def cube5 : LRATCatcher.Cube := [(52, true), (150, false), (72, true), (85, true)]
def cube6 : LRATCatcher.Cube := [(52, true), (150, false), (72, true), (85, false)]
def cube7 : LRATCatcher.Cube := [(52, true), (150, false), (72, false), (85, true)]
def cube8 : LRATCatcher.Cube := [(52, true), (150, false), (72, false), (85, false)]
def cube9 : LRATCatcher.Cube := [(52, false), (150, true), (72, true), (85, true)]
def cube10 : LRATCatcher.Cube := [(52, false), (150, true), (72, true), (85, false)]
def cube11 : LRATCatcher.Cube := [(52, false), (150, true), (72, false), (85, true)]
def cube12 : LRATCatcher.Cube := [(52, false), (150, true), (72, false), (85, false)]
def cube13 : LRATCatcher.Cube := [(52, false), (150, false), (72, true), (85, true)]
def cube14 : LRATCatcher.Cube := [(52, false), (150, false), (72, true), (85, false)]
def cube15 : LRATCatcher.Cube := [(52, false), (150, false), (72, false), (85, true)]
def cube16 : LRATCatcher.Cube := [(52, false), (150, false), (72, false), (85, false)]

def cubes : List LRATCatcher.Cube := [cube1, cube2, cube3, cube4, cube5, cube6, cube7, cube8, cube9, cube10, cube11, cube12, cube13, cube14, cube15, cube16]

end Biplanar.A4M07S
