import Biplanar.Instances.A4M13S.Base

/-! Leaf 9 of `a4_m13s`: its own witness set (260887 witnesses, the LRAT core
    of the Python-side solve of cube 9) and formula `F9`. -/

namespace Biplanar.A4M13S

def witnessStr9 : String := include_str "../../../data/a4_m13s/w9.txt"

def ws9 : List Biplanar.Witness := Biplanar.parseWitnesses witnessStr9

def F9 : Std.Sat.CNF Nat := Biplanar.mkCNFSym₀ G ws9 gens

end Biplanar.A4M13S
