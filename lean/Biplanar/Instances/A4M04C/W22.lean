import Biplanar.Instances.A4M04C.Base

/-! Leaf 22 of `a4_m04c`: its own witness set (700 witnesses, the LRAT core
    of the Python-side solve of cube 22) and formula `F22`. -/

namespace Biplanar.A4M04C

def witnessStr22 : String := include_str "../../../data/a4_m04c/w22.txt"

def ws22 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr22

def F22 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws22 gens

end Biplanar.A4M04C
