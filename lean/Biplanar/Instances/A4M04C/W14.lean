import Biplanar.Instances.A4M04C.Base

/-! Leaf 14 of `a4_m04c`: its own witness set (312554 witnesses, the LRAT core
    of the Python-side solve of cube 14) and formula `F14`. -/

namespace Biplanar.A4M04C

def witnessStr14 : String := include_str "../../../data/a4_m04c/w14.txt"

def ws14 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr14

def F14 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws14 gens

end Biplanar.A4M04C
