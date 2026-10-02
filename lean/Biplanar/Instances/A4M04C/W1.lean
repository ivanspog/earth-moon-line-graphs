import Biplanar.Instances.A4M04C.Base

/-! Leaf 1 of `a4_m04c`: its own witness set (316198 witnesses, the LRAT core
    of the Python-side solve of cube 1) and formula `F1`. -/

namespace Biplanar.A4M04C

def witnessStr1 : String := include_str "../../../data/a4_m04c/w1.txt"

def ws1 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr1

def F1 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws1 gens

end Biplanar.A4M04C
