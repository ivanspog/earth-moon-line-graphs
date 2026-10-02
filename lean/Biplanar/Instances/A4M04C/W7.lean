import Biplanar.Instances.A4M04C.Base

/-! Leaf 7 of `a4_m04c`: its own witness set (399682 witnesses, the LRAT core
    of the Python-side solve of cube 7) and formula `F7`. -/

namespace Biplanar.A4M04C

def witnessStr7 : String := include_str "../../../data/a4_m04c/w7.txt"

def ws7 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr7

def F7 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws7 gens

end Biplanar.A4M04C
