import Biplanar.Instances.A4M04C.Base

/-! Leaf 20 of `a4_m04c`: its own witness set (184 witnesses, the LRAT core
    of the Python-side solve of cube 20) and formula `F20`. -/

namespace Biplanar.A4M04C

def witnessStr20 : String := include_str "../../../data/a4_m04c/w20.txt"

def ws20 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr20

def F20 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws20 gens

end Biplanar.A4M04C
