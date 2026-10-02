import Biplanar.Instances.A4M09C.Base

/-! Leaf 2 of `a4_m09c`: its own witness set (358294 witnesses, the LRAT core
    of the Python-side solve of cube 2) and formula `F2`. -/

namespace Biplanar.A4M09C

def witnessStr2 : String := include_str "../../../data/a4_m09c/w2.txt"

def ws2 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr2

def F2 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws2 gens

end Biplanar.A4M09C
