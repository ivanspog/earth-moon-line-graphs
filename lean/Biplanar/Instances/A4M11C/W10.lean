import Biplanar.Instances.A4M11C.Base

/-! Leaf 10 of `a4_m11c`: its own witness set (321924 witnesses, the LRAT core
    of the Python-side solve of cube 10) and formula `F10`. -/

namespace Biplanar.A4M11C

def witnessStr10 : String := include_str "../../../data/a4_m11c/w10.txt"

def ws10 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr10

def F10 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws10 gens

end Biplanar.A4M11C
