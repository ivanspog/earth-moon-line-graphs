import Biplanar.Enum.Defs

/-!
# Biplanar.Enum.Gen — complete generators for the root enumerations

`forall5 P` and `forall7 P` evaluate `P` on a finite list of candidate vectors, built row by row
(the multiplicities of the pairs `(r, w)`, `w > r`, of vertex `r`) as bounded compositions.
`forall5_complete` / `forall7_complete`: if `forall5 P = true` then `P a = true` for every
`a` with `valid5 a = true` (resp. 7). Only the degree conditions are used here; the leaves may
include invalid vectors, so callers evaluate `!valid a || check a`.
-/

namespace Biplanar.Enum

/-- `xs` and `caps` have the same length and `xs[i] ≤ caps[i]` for every `i`. -/
def capsOK : List Nat → List Nat → Prop
  | [], [] => True
  | x :: xs, c :: cs => x ≤ c ∧ capsOK xs cs
  | _, _ => False

/-- Lists `xs` of length `caps.length` with `xs[i] ≤ caps[i]` and sum exactly `n`. -/
def bcomps : Nat → List Nat → List (List Nat)
  | n, [] => if n = 0 then [[]] else []
  | n, c :: cs => (List.range (min c n + 1)).flatMap (fun x => (bcomps (n - x) cs).map (x :: ·))

/-- Lists `xs` of length `caps.length` with `xs[i] ≤ caps[i]` and sum at most `n`. -/
def bsubs : Nat → List Nat → List (List Nat)
  | _, [] => [[]]
  | n, c :: cs => (List.range (min c n + 1)).flatMap (fun x => (bsubs (n - x) cs).map (x :: ·))

theorem mem_bcomps : ∀ (caps xs : List Nat) (n : Nat),
    capsOK xs caps → xs.sum = n → xs ∈ bcomps n caps
  | [], [], n, _, hs => by simp at hs; subst hs; simp [bcomps]
  | c :: cs, x :: xs, n, h, hs => by
    obtain ⟨hx, hr⟩ := h
    simp only [List.sum_cons] at hs
    simp only [bcomps, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨x, by omega, xs, mem_bcomps cs xs (n - x) hr (by omega), rfl⟩
  | [], _ :: _, _, h, _ => (h : False).elim
  | _ :: _, [], _, h, _ => (h : False).elim

theorem mem_bsubs : ∀ (caps xs : List Nat) (n : Nat),
    capsOK xs caps → xs.sum ≤ n → xs ∈ bsubs n caps
  | [], [], _, _, _ => by simp [bsubs]
  | c :: cs, x :: xs, n, h, hs => by
    obtain ⟨hx, hr⟩ := h
    simp only [List.sum_cons] at hs
    simp only [bsubs, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨x, by omega, xs, mem_bsubs cs xs (n - x) hr (by omega), rfl⟩
  | [], _ :: _, _, h, _ => (h : False).elim
  | _ :: _, [], _, h, _ => (h : False).elim

/-! ## Five vertices: pairs 01 02 03 04 12 13 14 23 24 34 = y0 … y9 -/

def forall5 (P : List Nat → Bool) : Bool :=
  (bsubs 8 [8, 8, 8, 8]).all fun r0 => match r0 with
  | [y0, y1, y2, y3] =>
    (bsubs (8 - y0) [8 - y1, 8 - y2, 8 - y3]).all fun r1 => match r1 with
    | [y4, y5, y6] =>
      (bsubs (8 - y1 - y4) [8 - y2 - y5, 8 - y3 - y6]).all fun r2 => match r2 with
      | [y7, y8] =>
        (bsubs (8 - y2 - y5 - y7) [8 - y3 - y6 - y8]).all fun r3 => match r3 with
        | [y9] => P [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9]
        | _ => true
      | _ => true
    | _ => true
  | _ => true

theorem len10 : ∀ (a : List Nat), a.length = 10 →
    ∃ y0 y1 y2 y3 y4 y5 y6 y7 y8 y9, a = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9]
  | [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9], _ => ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
  | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h | [_, _, _, _, _, _, _, _], h
  | [_, _, _, _, _, _, _, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h <;> omega

set_option maxHeartbeats 4000000 in
theorem forall5_complete (P : List Nat → Bool) (h : forall5 P = true) (a : List Nat)
    (ha : valid5 a = true) : P a = true := by
  simp only [valid5, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at ha
  obtain ⟨⟨⟨hl, hd⟩, _⟩, _⟩ := ha
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, rfl⟩ := len10 a hl
  have d0 : 0 + y0 + y1 + y2 + y3 ≤ 8 := hd 0 (by decide)
  have d1 : 0 + y0 + y4 + y5 + y6 ≤ 8 := hd 1 (by decide)
  have d2 : 0 + y1 + y4 + y7 + y8 ≤ 8 := hd 2 (by decide)
  have d3 : 0 + y2 + y5 + y7 + y9 ≤ 8 := hd 3 (by decide)
  have d4 : 0 + y3 + y6 + y8 + y9 ≤ 8 := hd 4 (by decide)
  simp only [forall5, List.all_eq_true] at h
  have h1 := h [y0, y1, y2, y3] (mem_bsubs _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h1
  have h2 := h1 [y4, y5, y6] (mem_bsubs _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h2
  have h3 := h2 [y7, y8] (mem_bsubs _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h3
  exact h3 [y9] (mem_bsubs _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))

/-! ## Seven vertices: pairs 01 … 06 = x0 … x5, 12 … 16 = x6 … x10, 23 … 26 = x11 … x14,
    34 35 36 = x15 x16 x17, 45 46 = x18 x19, 56 = x20 -/

def forall7 (P : List Nat → Bool) : Bool :=
  (bcomps 8 [8, 8, 8, 8, 8, 8]).all fun r0 => match r0 with
  | [x0, x1, x2, x3, x4, x5] =>
    (bcomps (8 - x0) [8 - x1, 8 - x2, 8 - x3, 8 - x4, 8 - x5]).all fun r1 => match r1 with
    | [x6, x7, x8, x9, x10] =>
      (bcomps (8 - x1 - x6) [8 - x2 - x7, 8 - x3 - x8, 8 - x4 - x9, 8 - x5 - x10]).all
        fun r2 => match r2 with
      | [x11, x12, x13, x14] =>
        (bcomps (8 - x2 - x7 - x11) [8 - x3 - x8 - x12, 8 - x4 - x9 - x13,
            8 - x5 - x10 - x14]).all fun r3 => match r3 with
        | [x15, x16, x17] =>
          (bcomps (8 - x3 - x8 - x12 - x15) [8 - x4 - x9 - x13 - x16,
              8 - x5 - x10 - x14 - x17]).all fun r4 => match r4 with
          | [x18, x19] =>
            (bcomps (8 - x4 - x9 - x13 - x16 - x18) [8 - x5 - x10 - x14 - x17 - x19]).all
              fun r5 => match r5 with
            | [x20] => P [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
                x16, x17, x18, x19, x20]
            | _ => true
          | _ => true
        | _ => true
      | _ => true
    | _ => true
  | _ => true

theorem cons_of_len {a : List Nat} {n : Nat} (h : a.length = n + 1) :
    ∃ x t, a = x :: t ∧ t.length = n := by
  cases a with
  | nil => simp at h
  | cons x t => exact ⟨x, t, rfl, by simpa using h⟩

theorem len21 (a : List Nat) (h : a.length = 21) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20,
      a = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18,
        x19, x20] := by
  obtain ⟨x0, a0, rfl, h0⟩ := cons_of_len (n := 20) h
  obtain ⟨x1, a1, rfl, h1⟩ := cons_of_len (n := 19) h0
  obtain ⟨x2, a2, rfl, h2⟩ := cons_of_len (n := 18) h1
  obtain ⟨x3, a3, rfl, h3⟩ := cons_of_len (n := 17) h2
  obtain ⟨x4, a4, rfl, h4⟩ := cons_of_len (n := 16) h3
  obtain ⟨x5, a5, rfl, h5⟩ := cons_of_len (n := 15) h4
  obtain ⟨x6, a6, rfl, h6⟩ := cons_of_len (n := 14) h5
  obtain ⟨x7, a7, rfl, h7⟩ := cons_of_len (n := 13) h6
  obtain ⟨x8, a8, rfl, h8⟩ := cons_of_len (n := 12) h7
  obtain ⟨x9, a9, rfl, h9⟩ := cons_of_len (n := 11) h8
  obtain ⟨x10, a10, rfl, h10⟩ := cons_of_len (n := 10) h9
  obtain ⟨x11, a11, rfl, h11⟩ := cons_of_len (n := 9) h10
  obtain ⟨x12, a12, rfl, h12⟩ := cons_of_len (n := 8) h11
  obtain ⟨x13, a13, rfl, h13⟩ := cons_of_len (n := 7) h12
  obtain ⟨x14, a14, rfl, h14⟩ := cons_of_len (n := 6) h13
  obtain ⟨x15, a15, rfl, h15⟩ := cons_of_len (n := 5) h14
  obtain ⟨x16, a16, rfl, h16⟩ := cons_of_len (n := 4) h15
  obtain ⟨x17, a17, rfl, h17⟩ := cons_of_len (n := 3) h16
  obtain ⟨x18, a18, rfl, h18⟩ := cons_of_len (n := 2) h17
  obtain ⟨x19, a19, rfl, h19⟩ := cons_of_len (n := 1) h18
  obtain ⟨x20, a20, rfl, h20⟩ := cons_of_len (n := 0) h19
  obtain rfl := List.eq_nil_of_length_eq_zero h20
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18,
    x19, x20, rfl⟩

set_option maxHeartbeats 8000000 in
theorem forall7_complete (P : List Nat → Bool) (h : forall7 P = true) (a : List Nat)
    (ha : valid7 a = true) : P a = true := by
  simp only [valid7, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ha
  obtain ⟨⟨hl, hd⟩, _⟩ := ha
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18,
    x19, x20, rfl⟩ := len21 a hl
  have d0 : 0 + x0 + x1 + x2 + x3 + x4 + x5 = 8 := hd 0 (by decide)
  have d1 : 0 + x0 + x6 + x7 + x8 + x9 + x10 = 8 := hd 1 (by decide)
  have d2 : 0 + x1 + x6 + x11 + x12 + x13 + x14 = 8 := hd 2 (by decide)
  have d3 : 0 + x2 + x7 + x11 + x15 + x16 + x17 = 8 := hd 3 (by decide)
  have d4 : 0 + x3 + x8 + x12 + x15 + x18 + x19 = 8 := hd 4 (by decide)
  have d5 : 0 + x4 + x9 + x13 + x16 + x18 + x20 = 8 := hd 5 (by decide)
  have d6 : 0 + x5 + x10 + x14 + x17 + x19 + x20 = 8 := hd 6 (by decide)
  simp only [forall7, List.all_eq_true] at h
  have h1 := h [x0, x1, x2, x3, x4, x5] (mem_bcomps _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h1
  have h2 := h1 [x6, x7, x8, x9, x10] (mem_bcomps _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h2
  have h3 := h2 [x11, x12, x13, x14] (mem_bcomps _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h3
  have h4 := h3 [x15, x16, x17] (mem_bcomps _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h4
  have h5 := h4 [x18, x19] (mem_bcomps _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))
  simp only [List.all_eq_true] at h5
  exact h5 [x20] (mem_bcomps _ _ _
    (by simp only [capsOK, and_true]; omega)
    (by simp only [List.sum_cons, List.sum_nil]; omega))

end Biplanar.Enum
