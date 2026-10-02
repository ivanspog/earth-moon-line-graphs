import Biplanar.Instances.A4M11C.Base

/-! Leaf 8 of `a4_m11c`: its own witness set (136102 witnesses, the LRAT core
    of the Python-side solve of cube 8) and formula `F8`. -/

namespace Biplanar.A4M11C

def witnessStr8 : String := include_str "../../../data/a4_m11c/w8.txt"

def ws8 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr8

def F8 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws8 gens

end Biplanar.A4M11C
