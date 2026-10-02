import Biplanar.Instances.A4M09C.Base

/-! Leaf 5 of `a4_m09c`: its own witness set (421616 witnesses, the LRAT core
    of the Python-side solve of cube 5) and formula `F5`. -/

namespace Biplanar.A4M09C

def witnessStr5 : String := include_str "../../../data/a4_m09c/w5.txt"

def ws5 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr5

def F5 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws5 gens

end Biplanar.A4M09C
