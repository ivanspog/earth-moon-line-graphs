import Biplanar.Instances.A4M11C.Base

/-! Leaf 15 of `a4_m11c`: its own witness set (226 witnesses, the LRAT core
    of the Python-side solve of cube 15) and formula `F15`. -/

namespace Biplanar.A4M11C

def witnessStr15 : String := include_str "../../../data/a4_m11c/w15.txt"

def ws15 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr15

def F15 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws15 gens

end Biplanar.A4M11C
