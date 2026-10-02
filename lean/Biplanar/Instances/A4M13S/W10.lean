import Biplanar.Instances.A4M13S.Base

/-! Leaf 10 of `a4_m13s`: its own witness set (255847 witnesses, the LRAT core
    of the Python-side solve of cube 10) and formula `F10`. -/

namespace Biplanar.A4M13S

def witnessStr10 : String := include_str "../../../data/a4_m13s/w10.txt"

def ws10 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr10

def F10 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws10 gens

end Biplanar.A4M13S
