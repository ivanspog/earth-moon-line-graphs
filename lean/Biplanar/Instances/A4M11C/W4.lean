import Biplanar.Instances.A4M11C.Base

/-! Leaf 4 of `a4_m11c`: its own witness set (126490 witnesses, the LRAT core
    of the Python-side solve of cube 4) and formula `F4`. -/

namespace Biplanar.A4M11C

def witnessStr4 : String := include_str "../../../data/a4_m11c/w4.txt"

def ws4 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr4

def F4 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws4 gens

end Biplanar.A4M11C
