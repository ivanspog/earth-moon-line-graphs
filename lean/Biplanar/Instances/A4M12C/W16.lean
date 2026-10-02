import Biplanar.Instances.A4M12C.Base

/-! Leaf 16 of `a4_m12c`: its own witness set (42 witnesses, the LRAT core
    of the Python-side solve of cube 16) and formula `F16`. -/

namespace Biplanar.A4M12C

def witnessStr16 : String := include_str "../../../data/a4_m12c/w16.txt"

def ws16 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr16

def F16 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws16 gens

end Biplanar.A4M12C
