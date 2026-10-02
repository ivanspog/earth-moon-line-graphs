import Biplanar.Instances.A4M12C.Base

/-! The 18 cubes of `a4_m12c` (DIMACS: [[-105, -53, -95, -149], [-105, -53, -95, 149, -129, -106], [-105, -53, -95, 149, -129, 106], [-105, -53, -95, 149, 129], [-105, -53, 95, -149], [-105, -53, 95, 149], [-105, 53, -95, -149], [-105, 53, -95, 149], [-105, 53, 95, -149], [-105, 53, 95, 149], [105, -53, -95, -149], [105, -53, -95, 149], [105, -53, 95, -149], [105, -53, 95, 149], [105, 53, -95, -149], [105, 53, -95, 149], [105, 53, 95, -149], [105, 53, 95, 149]]). -/

namespace Biplanar.A4M12C

def cube1 : LRATCatcher.Cube := [(104, false), (52, false), (94, false), (148, false)]
def cube2 : LRATCatcher.Cube := [(104, false), (52, false), (94, false), (148, true), (128, false), (105, false)]
def cube3 : LRATCatcher.Cube := [(104, false), (52, false), (94, false), (148, true), (128, false), (105, true)]
def cube4 : LRATCatcher.Cube := [(104, false), (52, false), (94, false), (148, true), (128, true)]
def cube5 : LRATCatcher.Cube := [(104, false), (52, false), (94, true), (148, false)]
def cube6 : LRATCatcher.Cube := [(104, false), (52, false), (94, true), (148, true)]
def cube7 : LRATCatcher.Cube := [(104, false), (52, true), (94, false), (148, false)]
def cube8 : LRATCatcher.Cube := [(104, false), (52, true), (94, false), (148, true)]
def cube9 : LRATCatcher.Cube := [(104, false), (52, true), (94, true), (148, false)]
def cube10 : LRATCatcher.Cube := [(104, false), (52, true), (94, true), (148, true)]
def cube11 : LRATCatcher.Cube := [(104, true), (52, false), (94, false), (148, false)]
def cube12 : LRATCatcher.Cube := [(104, true), (52, false), (94, false), (148, true)]
def cube13 : LRATCatcher.Cube := [(104, true), (52, false), (94, true), (148, false)]
def cube14 : LRATCatcher.Cube := [(104, true), (52, false), (94, true), (148, true)]
def cube15 : LRATCatcher.Cube := [(104, true), (52, true), (94, false), (148, false)]
def cube16 : LRATCatcher.Cube := [(104, true), (52, true), (94, false), (148, true)]
def cube17 : LRATCatcher.Cube := [(104, true), (52, true), (94, true), (148, false)]
def cube18 : LRATCatcher.Cube := [(104, true), (52, true), (94, true), (148, true)]

def cubes : List LRATCatcher.Cube := [cube1, cube2, cube3, cube4, cube5, cube6, cube7, cube8, cube9, cube10, cube11, cube12, cube13, cube14, cube15, cube16, cube17, cube18]

end Biplanar.A4M12C
