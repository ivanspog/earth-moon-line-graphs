import Biplanar.Instances.A4M04C.Base

/-! Leaf 17 of `a4_m04c`: its own witness set (4 witnesses, the LRAT core
    of the Python-side solve of cube 17) and formula `F17`. -/

namespace Biplanar.A4M04C

def witnessStr17 : String := include_str "../../../data/a4_m04c/w17.txt"

def ws17 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr17

def F17 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws17 gens

end Biplanar.A4M04C
