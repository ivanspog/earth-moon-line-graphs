import Biplanar.Enum.Check

/-!
# Biplanar.Enum.Main — the two root enumerations, machine-checked

* `five_not_biplanar` is fact (F5) of the paper: every 5-vertex root with maximum degree ≤ 8,
  triple sums ≤ 8 and 19 or 20 edges has a non-biplanar line graph.
* `seven_cases` is the computational part of fact (F32): for every 8-regular 7-vertex root with
  triple sums ≤ 8 and `sumC2 ≥ 40`, the line graph is either refuted outright by an Euler or a
  triangle-free witness, or it is isomorphic (by a checked vertex map) to one of the 22 graphs of
  the certified theorems `Biplanar.A4M<i>.not_biplanar` (listed in `a4Graphs`).
  `Biplanar.Enum.Final` combines it with those 22 theorems.

Hypotheses on `planar`: (H4) `EulerHyp`, (H5) `TriFreeHyp` (see `Biplanar.Enum.Defs`).
The two `native_decide` calls evaluate the complete generators of `Biplanar.Enum.Gen`
(7.1 × 10⁶ and ≈ 7.9 × 10⁸ search nodes) as native code (`precompileModules`).
-/

namespace Biplanar.Enum
open Biplanar

theorem all5 : forall5 check5 = true := by native_decide

theorem all7 : forall7 check7 = true := by native_decide

theorem five_not_biplanar (planar : List Edge → Prop) (HE : EulerHyp planar)
    (HT : TriFreeHyp planar) (a : List Nat) (ha : valid5 a = true) :
    ¬ Biplanar planar (lineGraph 5 a) := by
  have hc := forall5_complete check5 all5 a ha
  simp only [check5, ha, Bool.not_true, Bool.false_or] at hc
  rcases checkWith_sound hc with h | ⟨h, _⟩
  · exact refuted_sound HE HT h
  · exact absurd h (by decide)

theorem seven_cases (planar : List Edge → Prop) (HE : EulerHyp planar)
    (HT : TriFreeHyp planar) (a : List Nat) (ha : valid7 a = true) (h40 : 40 ≤ sumC2 a) :
    ¬ Biplanar planar (lineGraph 7 a) ∨
      ∃ i π, isoOK (lineGraph 7 a) (a4Graphs.getD i ⟨0, []⟩) π = true := by
  have hc := forall7_complete check7 all7 a ha
  have hlt : decide (sumC2 a < 40) = false := by simp only [decide_eq_false_iff_not]; omega
  simp only [check7, hlt, ha, Bool.not_true, Bool.false_or] at hc
  rcases checkWith_sound hc with h | ⟨_, h⟩
  · exact Or.inl (refuted_sound HE HT h)
  · exact Or.inr h

end Biplanar.Enum

#print axioms Biplanar.Enum.five_not_biplanar
#print axioms Biplanar.Enum.seven_cases
