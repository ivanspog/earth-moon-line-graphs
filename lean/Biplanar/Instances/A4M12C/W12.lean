import Biplanar.Instances.A4M12C.Base

/-! Leaf 12 of `a4_m12c`: its own witness set (1 witnesses, the LRAT core
    of the Python-side solve of cube 12) and formula `F12`. -/

namespace Biplanar.A4M12C

def witnessStr12 : String := include_str "../../../data/a4_m12c/w12.txt"

def ws12 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr12

def F12 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws12 gens

end Biplanar.A4M12C
