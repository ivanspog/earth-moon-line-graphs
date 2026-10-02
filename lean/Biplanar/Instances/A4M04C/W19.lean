import Biplanar.Instances.A4M04C.Base

/-! Leaf 19 of `a4_m04c`: its own witness set (479 witnesses, the LRAT core
    of the Python-side solve of cube 19) and formula `F19`. -/

namespace Biplanar.A4M04C

def witnessStr19 : String := include_str "../../../data/a4_m04c/w19.txt"

def ws19 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr19

def F19 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws19 gens

end Biplanar.A4M04C
