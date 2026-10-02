import Biplanar.Instances.A4M13S.Base

/-! Leaf 3 of `a4_m13s`: its own witness set (207412 witnesses, the LRAT core
    of the Python-side solve of cube 3) and formula `F3`. -/

namespace Biplanar.A4M13S

def witnessStr3 : String := include_str "../../../data/a4_m13s/w3.txt"

def ws3 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr3

def F3 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws3 gens

end Biplanar.A4M13S
