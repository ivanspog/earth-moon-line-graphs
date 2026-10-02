import Biplanar.Instances.A4M04C.Base

/-! Leaf 16 of `a4_m04c`: its own witness set (223 witnesses, the LRAT core
    of the Python-side solve of cube 16) and formula `F16`. -/

namespace Biplanar.A4M04C

def witnessStr16 : String := include_str "../../../data/a4_m04c/w16.txt"

def ws16 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr16

def F16 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws16 gens

end Biplanar.A4M04C
