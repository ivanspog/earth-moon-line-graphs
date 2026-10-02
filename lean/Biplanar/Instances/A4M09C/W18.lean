import Biplanar.Instances.A4M09C.Base

/-! Leaf 18 of `a4_m09c`: its own witness set (1 witnesses, the LRAT core
    of the Python-side solve of cube 18) and formula `F18`. -/

namespace Biplanar.A4M09C

def witnessStr18 : String := include_str "../../../data/a4_m09c/w18.txt"

def ws18 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr18

def F18 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws18 gens

end Biplanar.A4M09C
