import Biplanar.Enum.Main

/-!
# Biplanar.Enum.Close — (F32) given the 22 certified graphs

`seven_not_biplanar_of`: if the 22 graphs `a4Graphs` are not biplanar, then no 8-regular root on
7 vertices with triple sums ≤ 8 and `sumC2 ≥ 40` has a biplanar line graph. The hypothesis `hA4`
is discharged by the 22 theorems `Biplanar.A4M<i>.not_biplanar` in `Biplanar.EnumFinal`.
-/

namespace Biplanar.Enum
open Biplanar

theorem seven_not_biplanar_of (planar : List Edge → Prop)
    (H3 : ∀ G : Graph, IsoInvariant G planar) (HE : EulerHyp planar) (HT : TriFreeHyp planar)
    (hA4 : ∀ i, i < 22 → ¬ Biplanar planar (a4Graphs.getD i ⟨0, []⟩))
    (a : List Nat) (ha : valid7 a = true) (h40 : 40 ≤ sumC2 a) :
    ¬ Biplanar planar (lineGraph 7 a) := by
  rcases seven_cases planar HE HT a ha h40 with h | ⟨i, π, hiso⟩
  · exact h
  · intro hb
    have hb' := iso_sound (H3 _) hiso hb
    by_cases hi : i < 22
    · exact hA4 i hi hb'
    · have hlen : a4Graphs.length = 22 := by rfl
      have hd : a4Graphs.getD i ⟨0, []⟩ = ⟨0, []⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [hd] at hiso
      simp [isoOK, graphOK] at hiso

end Biplanar.Enum

#print axioms Biplanar.Enum.seven_not_biplanar_of
