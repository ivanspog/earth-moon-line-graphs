import Biplanar.Instances.A4M11C.Base

/-! Leaf 6 of `a4_m11c`: its own witness set (461099 witnesses, the LRAT core
    of the Python-side solve of cube 6) and formula `F6`. -/

namespace Biplanar.A4M11C

def witnessStr6 : String := include_str "../../../data/a4_m11c/w6.txt"

def ws6 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr6

def F6 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws6 gens

end Biplanar.A4M11C
