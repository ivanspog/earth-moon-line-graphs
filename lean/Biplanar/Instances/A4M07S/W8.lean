import Biplanar.Instances.A4M07S.Base

/-! Leaf 8 of `a4_m07s`: its own witness set (845 witnesses, the LRAT core
    of the Python-side solve of cube 8) and formula `F8`. -/

namespace Biplanar.A4M07S

def witnessStr8 : String := include_str "../../../data/a4_m07s/w8.txt"

def ws8 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr8

def F8 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws8 gens

end Biplanar.A4M07S
