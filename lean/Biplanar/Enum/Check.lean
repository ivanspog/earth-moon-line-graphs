import Biplanar.Enum.Sound
import Biplanar.Enum.Gen
import Biplanar.Enum.Data
import Std.Data.HashMap

/-!
# Biplanar.Enum.Check — per-vector checks and what they prove

For a vector `a`, `checkWith` looks up a class representative `r` and a relabelling `τ` with
`a = τ·r` (lookup table built from `reps × all permutations`; untrusted), transports the
representative's certificate to `lineGraph k a` along the induced vertex map `ρ`, and checks the
transported certificate on `lineGraph k a` itself. Soundness (`checkWith_sound`) only uses the
final checkers of `Biplanar.Enum.Sound`, so the lookup, `τ`, `ρ` and the data are untrusted.
-/

namespace Biplanar.Enum
open Biplanar

/-! ## Untrusted helpers -/

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (fun p =>
      (List.range (p.length + 1)).map (fun i => p.take i ++ x :: p.drop i))

/-- Index of the pair `{u, v}` in `pairsOf k`. -/
def pidx (k u v : Nat) : Nat :=
  let a := min u v; let b := max u v
  a * (2 * k - a - 1) / 2 + (b - a - 1)

/-- The multiplicity vector relabelled by `τ` (vertex `i ↦ τ[i]`). -/
def relabel (k : Nat) (τ r : List Nat) : List Nat :=
  ((pairsOf k).zip r).foldl (fun (arr : Array Nat) pm =>
      arr.set! (pidx k (τ.getD pm.1.1 0) (τ.getD pm.1.2 0)) pm.2)
    (List.replicate (pairsOf k).length 0).toArray |>.toList

def table (k : Nat) (reps : List (List Nat)) : Std.HashMap (List Nat) (Nat × List Nat) :=
  let ps := perms (List.range k)
  (List.range reps.length).foldl (fun m i =>
    ps.foldl (fun m τ => m.insert (relabel k τ (reps.getD i [])) (i, τ)) m) {}

/-- Prefix sums: `offsets a = [0, a₀, a₀ + a₁, …]`. -/
def offsets (a : List Nat) : Array Nat :=
  (a.foldl (fun (p : Array Nat × Nat) x => (p.1.push p.2, p.2 + x)) (#[], 0)).1

/-- The vertex map `L(r) → L(a)` induced by `τ` (copies matched in order). -/
def copyMap (k : Nat) (τ r a : List Nat) : List Nat :=
  let P := pairsOf k
  let offA := offsets a
  (List.range P.length).flatMap (fun t =>
    let p := P.getD t (0, 0)
    let t' := pidx k (τ.getD p.1 0) (τ.getD p.2 0)
    (List.range (r.getD t 0)).map (fun c => offA[t']! + c))

def invPerm (ρ : List Nat) : List Nat :=
  ((List.range ρ.length).foldl (fun (arr : Array Nat) x => arr.set! (ρ.getD x 0) x)
    (List.replicate ρ.length 0).toArray).toList

/-- `(compose π σ)[i] = π[σ[i]]`. -/
def compose (π σ : List Nat) : List Nat := σ.map (fun y => π.getD y y)

/-! ## Checks -/

def certCheck (allowIso : Bool) (k : Nat) (a : List Nat) (ρ : List Nat) : Cert → Bool
  | .euler W => eulerWitOK (lineGraph k a) (W.map (fun x => ρ.getD x x))
  | .tf W T => tfWitOK (lineGraph k a) (W.map (fun x => ρ.getD x x)) (T.map (applyPerm ρ))
  | .iso i π => allowIso && isoOK (lineGraph k a) (a4Graphs.getD i ⟨0, []⟩) (compose π (invPerm ρ))

def checkWith (allowIso : Bool) (k : Nat) (tbl : Std.HashMap (List Nat) (Nat × List Nat))
    (reps : List (List Nat)) (certs : List Cert) (a : List Nat) : Bool :=
  match tbl[a]? with
  | none => false
  | some (i, τ) => certCheck allowIso k a (copyMap k τ (reps.getD i []) a) (certs.getD i default)

def table5 : Std.HashMap (List Nat) (Nat × List Nat) := table 5 reps5
def table7 : Std.HashMap (List Nat) (Nat × List Nat) := table 7 reps7

def check5 (a : List Nat) : Bool := !valid5 a || checkWith false 5 table5 reps5 certs5 a

/-- Vacuous when `sumC2 a < 40` (Euler's bound on the whole line graph, by hand). -/
def check7 (a : List Nat) : Bool :=
  decide (sumC2 a < 40) || !valid7 a || checkWith true 7 table7 reps7 certs7 a

/-! ## Soundness of the checks -/

/-- What a passing check proves. -/
def Refuted (k : Nat) (a : List Nat) : Prop :=
  (∃ W, eulerWitOK (lineGraph k a) W = true) ∨ (∃ W T, tfWitOK (lineGraph k a) W T = true)

theorem certCheck_sound {allowIso k a ρ} {c : Cert} (h : certCheck allowIso k a ρ c = true) :
    Refuted k a ∨ (allowIso = true ∧
      ∃ i π, isoOK (lineGraph k a) (a4Graphs.getD i ⟨0, []⟩) π = true) := by
  cases c with
  | euler W => exact Or.inl (Or.inl ⟨_, h⟩)
  | tf W T => exact Or.inl (Or.inr ⟨_, _, h⟩)
  | iso i π =>
    simp only [certCheck, Bool.and_eq_true] at h
    exact Or.inr ⟨h.1, i, _, h.2⟩

theorem checkWith_sound {allowIso k tbl reps certs a}
    (h : checkWith allowIso k tbl reps certs a = true) :
    Refuted k a ∨ (allowIso = true ∧
      ∃ i π, isoOK (lineGraph k a) (a4Graphs.getD i ⟨0, []⟩) π = true) := by
  unfold checkWith at h
  split at h
  · exact absurd h (by decide)
  · exact certCheck_sound h

theorem refuted_sound {planar : List Edge → Prop} (HE : EulerHyp planar)
    (HT : TriFreeHyp planar) {k a} (h : Refuted k a) : ¬ Biplanar planar (lineGraph k a) := by
  rcases h with ⟨W, hW⟩ | ⟨W, T, hT⟩
  · exact euler_sound HE hW
  · exact tf_sound HT hT

end Biplanar.Enum
