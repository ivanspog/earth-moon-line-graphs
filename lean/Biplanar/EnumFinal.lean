import Biplanar.Enum.Close
import Biplanar.Instances.A4M00
import Biplanar.Instances.A4M01
import Biplanar.Instances.A4M02
import Biplanar.Instances.A4M03
import Biplanar.Instances.A4M04C
import Biplanar.Instances.A4M05
import Biplanar.Instances.A4M06
import Biplanar.Instances.A4M07S
import Biplanar.Instances.A4M08
import Biplanar.Instances.A4M09C
import Biplanar.Instances.A4M10
import Biplanar.Instances.A4M11C
import Biplanar.Instances.A4M12C
import Biplanar.Instances.A4M13S
import Biplanar.Instances.A4M14
import Biplanar.Instances.A4M15
import Biplanar.Instances.A4M16
import Biplanar.Instances.A4M17
import Biplanar.Instances.A4M18
import Biplanar.Instances.A4M19
import Biplanar.Instances.A4M20
import Biplanar.Instances.A4M21

/-!
# Biplanar.EnumFinal — the seven-vertex enumeration closed by the 22 certified theorems

`seven_not_biplanar`: for every 8-regular loopless root multigraph on 7 vertices with every triple
sum ≤ 8 and `∑ C(mult, 2) ≥ 40`, the line graph is not biplanar. Together with the hand step
"`sumC2 < 40` violates Euler's bound on the whole line graph" this is fact (F32) of the paper;
`Biplanar.Enum.five_not_biplanar` is fact (F5).

Hypotheses on `planar`: (H2) Kuratowski's elementary direction, (H3) isomorphism invariance
(`Biplanar.SymDefs`), (H4) Euler's bound and (H5) Euler's bound for triangle-free graphs
(`Biplanar.Enum.Defs`). Ordinary planarity satisfies all four.
-/

namespace Biplanar.Enum
open Biplanar

/-- The data copied into `Biplanar.Enum.Data` is exactly the graphs of the 22 certified theorems. -/
theorem a4Graphs_eq : a4Graphs = [A4M00.G, A4M01.G, A4M02.G, A4M03.G, A4M04C.G, A4M05.G, A4M06.G, A4M07S.G, A4M08.G, A4M09C.G, A4M10.G, A4M11C.G, A4M12C.G, A4M13S.G, A4M14.G, A4M15.G, A4M16.G, A4M17.G, A4M18.G, A4M19.G, A4M20.G, A4M21.G] := by rfl

theorem a4_not_biplanar (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (H3 : ∀ G : Graph, IsoInvariant G planar) :
    ∀ i, i < 22 → ¬ Biplanar planar (a4Graphs.getD i ⟨0, []⟩) := by
  rw [a4Graphs_eq]
  intro i hi
  have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4M00.not_biplanar planar H2 (H3 _)
  · exact A4M01.not_biplanar planar H2 (H3 _)
  · exact A4M02.not_biplanar planar H2 (H3 _)
  · exact A4M03.not_biplanar planar H2 (H3 _)
  · exact A4M04C.not_biplanar planar H2 (H3 _)
  · exact A4M05.not_biplanar planar H2 (H3 _)
  · exact A4M06.not_biplanar planar H2 (H3 _)
  · exact A4M07S.not_biplanar planar H2 (H3 _)
  · exact A4M08.not_biplanar planar H2 (H3 _)
  · exact A4M09C.not_biplanar planar H2 (H3 _)
  · exact A4M10.not_biplanar planar H2 (H3 _)
  · exact A4M11C.not_biplanar planar H2 (H3 _)
  · exact A4M12C.not_biplanar planar H2 (H3 _)
  · exact A4M13S.not_biplanar planar H2 (H3 _)
  · exact A4M14.not_biplanar planar H2 (H3 _)
  · exact A4M15.not_biplanar planar H2 (H3 _)
  · exact A4M16.not_biplanar planar H2 (H3 _)
  · exact A4M17.not_biplanar planar H2 (H3 _)
  · exact A4M18.not_biplanar planar H2 (H3 _)
  · exact A4M19.not_biplanar planar H2 (H3 _)
  · exact A4M20.not_biplanar planar H2 (H3 _)
  · exact A4M21.not_biplanar planar H2 (H3 _)

theorem seven_not_biplanar (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (H3 : ∀ G : Graph, IsoInvariant G planar) (HE : EulerHyp planar) (HT : TriFreeHyp planar)
    (a : List Nat) (ha : valid7 a = true) (h40 : 40 ≤ sumC2 a) :
    ¬ Biplanar planar (lineGraph 7 a) :=
  seven_not_biplanar_of planar H3 HE HT (a4_not_biplanar planar H2 H3) a ha h40

end Biplanar.Enum

#print axioms Biplanar.Enum.seven_not_biplanar
#print axioms Biplanar.Enum.five_not_biplanar
