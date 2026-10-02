import Biplanar.Instances.A4M04C.Base

/-! Leaf 21 of `a4_m04c`: its own witness set (6 witnesses, the LRAT core
    of the Python-side solve of cube 21) and formula `F21`. -/

namespace Biplanar.A4M04C

def witnessStr21 : String := include_str "../../../data/a4_m04c/w21.txt"

def ws21 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr21

def F21 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws21 gens

end Biplanar.A4M04C
