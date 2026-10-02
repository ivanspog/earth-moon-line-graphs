import Biplanar.Instances.A4M13S.Base

/-! Leaf 11 of `a4_m13s`: its own witness set (202492 witnesses, the LRAT core
    of the Python-side solve of cube 11) and formula `F11`. -/

namespace Biplanar.A4M13S

def witnessStr11 : String := include_str "../../../data/a4_m13s/w11.txt"

def ws11 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr11

def F11 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws11 gens

end Biplanar.A4M13S
