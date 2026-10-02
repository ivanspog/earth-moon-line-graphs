import Biplanar.Instances.A4M09C.Base

/-! The 18 cubes of `a4_m09c` (DIMACS: [[-101, -106, -108, -141], [-101, -106, -108, 141], [-101, -106, 108, -141], [-101, -106, 108, 141], [-101, 106, -108, -141], [-101, 106, -108, 141, -38, -59], [-101, 106, -108, 141, -38, 59], [-101, 106, -108, 141, 38], [-101, 106, 108, -141], [-101, 106, 108, 141], [101, -106, -108, -141], [101, -106, -108, 141], [101, -106, 108, -141], [101, -106, 108, 141], [101, 106, -108, -141], [101, 106, -108, 141], [101, 106, 108, -141], [101, 106, 108, 141]]). -/

namespace Biplanar.A4M09C

def cube1 : LRATCatcher.Cube := [(100, false), (105, false), (107, false), (140, false)]
def cube2 : LRATCatcher.Cube := [(100, false), (105, false), (107, false), (140, true)]
def cube3 : LRATCatcher.Cube := [(100, false), (105, false), (107, true), (140, false)]
def cube4 : LRATCatcher.Cube := [(100, false), (105, false), (107, true), (140, true)]
def cube5 : LRATCatcher.Cube := [(100, false), (105, true), (107, false), (140, false)]
def cube6 : LRATCatcher.Cube := [(100, false), (105, true), (107, false), (140, true), (37, false), (58, false)]
def cube7 : LRATCatcher.Cube := [(100, false), (105, true), (107, false), (140, true), (37, false), (58, true)]
def cube8 : LRATCatcher.Cube := [(100, false), (105, true), (107, false), (140, true), (37, true)]
def cube9 : LRATCatcher.Cube := [(100, false), (105, true), (107, true), (140, false)]
def cube10 : LRATCatcher.Cube := [(100, false), (105, true), (107, true), (140, true)]
def cube11 : LRATCatcher.Cube := [(100, true), (105, false), (107, false), (140, false)]
def cube12 : LRATCatcher.Cube := [(100, true), (105, false), (107, false), (140, true)]
def cube13 : LRATCatcher.Cube := [(100, true), (105, false), (107, true), (140, false)]
def cube14 : LRATCatcher.Cube := [(100, true), (105, false), (107, true), (140, true)]
def cube15 : LRATCatcher.Cube := [(100, true), (105, true), (107, false), (140, false)]
def cube16 : LRATCatcher.Cube := [(100, true), (105, true), (107, false), (140, true)]
def cube17 : LRATCatcher.Cube := [(100, true), (105, true), (107, true), (140, false)]
def cube18 : LRATCatcher.Cube := [(100, true), (105, true), (107, true), (140, true)]

def cubes : List LRATCatcher.Cube := [cube1, cube2, cube3, cube4, cube5, cube6, cube7, cube8, cube9, cube10, cube11, cube12, cube13, cube14, cube15, cube16, cube17, cube18]

end Biplanar.A4M09C
