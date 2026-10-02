import Biplanar.Instances.A4M07S.Base

/-! Leaf 5 of `a4_m07s`: its own witness set (881 witnesses, the LRAT core
    of the Python-side solve of cube 5) and formula `F5`. -/

namespace Biplanar.A4M07S

def witnessStr5 : String := include_str "../../../data/a4_m07s/w5.txt"

def ws5 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr5

def F5 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws5 gens

end Biplanar.A4M07S
