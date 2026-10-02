import Biplanar.Instances.A4M04C.Base

/-! Leaf 9 of `a4_m04c`: its own witness set (294342 witnesses, the LRAT core
    of the Python-side solve of cube 9) and formula `F9`. -/

namespace Biplanar.A4M04C

def witnessStr9 : String := include_str "../../../data/a4_m04c/w9.txt"

def ws9 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr9

def F9 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws9 gens

end Biplanar.A4M04C
