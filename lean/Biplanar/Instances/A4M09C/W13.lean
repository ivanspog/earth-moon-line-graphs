import Biplanar.Instances.A4M09C.Base

/-! Leaf 13 of `a4_m09c`: its own witness set (5 witnesses, the LRAT core
    of the Python-side solve of cube 13) and formula `F13`. -/

namespace Biplanar.A4M09C

def witnessStr13 : String := include_str "../../../data/a4_m09c/w13.txt"

def ws13 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr13

def F13 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws13 gens

end Biplanar.A4M09C
