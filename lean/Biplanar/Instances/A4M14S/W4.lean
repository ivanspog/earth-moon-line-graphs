import Biplanar.Instances.A4M14S.Base

/-! Leaf 4 of `a4_m14s`: its own witness set (34462 witnesses, the LRAT core
    of the Python-side solve of cube 4) and formula `F4`. -/

namespace Biplanar.A4M14S

def witnessStr4 : String := include_str "../../../data/a4_m14s/w4.txt"

def ws4 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr4

def F4 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws4 gens

end Biplanar.A4M14S
