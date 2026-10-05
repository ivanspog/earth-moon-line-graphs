import Biplanar.SymDefs

/-!
# Biplanar.Enum.Defs — the root enumerations of the line-graph theorem (trusted surface)

The line-graph theorem (P-008) reduces to two finite facts about small *root* multigraphs:

* (F5) every loopless multigraph on 5 vertices with maximum degree ≤ 8, every triple sum ≤ 8 and
  19 or 20 edges has a non-biplanar line graph;
* (F32) every 8-regular loopless multigraph on 7 vertices with every triple sum ≤ 8 and
  `∑ C(mult, 2) ≥ 40` has a non-biplanar line graph.

Everything a reader must audit to understand the statements of `Biplanar.Enum.Main` and
`Biplanar.Enum.Final` is in this file:

* a root multigraph on `k` vertices is a list `a` of multiplicities indexed by `pairsOf k`;
* `lineGraph k a` is its line graph, a `Biplanar.Graph`;
* `valid5`, `valid7`, `sumC2` are the conditions above;
* `EulerHyp` (H4) and `TriFreeHyp` (H5) are the two further elementary facts about `planar` used,
  besides (H2) Kuratowski's elementary direction and (H3) isomorphism invariance of
  `Biplanar.SymDefs`: a planar simple graph on `w ≥ 3` vertices has at most `3w − 6` edges, and at
  most `2w − 4` if it is triangle-free. Both follow from Euler's formula, and both are stated for
  the subgraph of `S` on a vertex list `W`.
-/

namespace Biplanar.Enum
open Biplanar

/-! ## Root multigraphs and their line graphs -/

/-- The vertex pairs `(i, j)` with `i < j < k`, in lexicographic order. -/
def pairsOf (k : Nat) : List (Nat × Nat) :=
  (List.range k).flatMap (fun i =>
    ((List.range k).filter (fun j => decide (i < j))).map (fun j => (i, j)))

/-- The edges of the root multigraph with multiplicity vector `a` (indexed like `pairsOf k`),
    each pair repeated by its multiplicity, in pair order. -/
def rootEdges (k : Nat) (a : List Nat) : List (Nat × Nat) :=
  ((pairsOf k).zip a).flatMap (fun pm => List.replicate pm.2 pm.1)

/-- Two root edges share an end. -/
def meets (p q : Nat × Nat) : Bool := p.1 == q.1 || p.1 == q.2 || p.2 == q.1 || p.2 == q.2

/-- The line graph: one vertex per root edge (numbered in the order of `rootEdges`), two vertices
    adjacent iff their root edges share an end (parallel root edges share both). -/
def lineGraph (k : Nat) (a : List Nat) : Graph :=
  let R := (rootEdges k a).toArray
  ⟨R.size, (List.range R.size).flatMap (fun x =>
    ((List.range R.size).filter (fun y => decide (x < y) && meets R[x]! R[y]!)).map
      (fun y => (x, y)))⟩

/-! ## The conditions -/

/-- Multiplicity of the pair `(u, v)`, `u < v`. -/
def mult (k : Nat) (a : List Nat) (u v : Nat) : Nat :=
  (((pairsOf k).zip a).filter (fun pm => pm.1 == (u, v))).foldl (fun s pm => s + pm.2) 0

/-- Degree of the vertex `v` (sum of the multiplicities of the pairs containing `v`). -/
def deg (k : Nat) (a : List Nat) (v : Nat) : Nat :=
  (((pairsOf k).zip a).filter (fun pm => pm.1.1 == v || pm.1.2 == v)).foldl (fun s pm => s + pm.2) 0

/-- Every three vertices span at most 8 edges. -/
def tripleOK (k : Nat) (a : List Nat) : Bool :=
  (List.range k).all fun u => (List.range k).all fun v => (List.range k).all fun w =>
    !(decide (u < v) && decide (v < w)) || decide (mult k a u v + mult k a u w + mult k a v w ≤ 8)

/-- (F5) roots: 5 vertices, maximum degree ≤ 8, triple sums ≤ 8, 19 or 20 edges. -/
def valid5 (a : List Nat) : Bool :=
  a.length == 10 && (List.range 5).all (fun v => decide (deg 5 a v ≤ 8)) && tripleOK 5 a &&
    (a.sum == 19 || a.sum == 20)

/-- (F32) roots: 7 vertices, 8-regular, triple sums ≤ 8. -/
def valid7 (a : List Nat) : Bool :=
  a.length == 21 && (List.range 7).all (fun v => deg 7 a v == 8) && tripleOK 7 a

/-- `∑ C(m, 2)` over the multiplicities. For an 8-regular root on 7 vertices the line graph has
    `196 − sumC2 a` edges, so Euler's bound `6·28 − 12 = 156` forces `sumC2 a ≥ 40`
    (paper, Lemma 3.2 step 2). -/
def sumC2 (a : List Nat) : Nat := (a.map (fun m => m * (m - 1) / 2)).sum

/-! ## The two Euler-type facts about `planar` -/

/-- Both ends of `e` lie in `W`. -/
def inside (W : List Nat) (e : Edge) : Bool := W.contains e.1 && W.contains e.2

/-- No three vertices `x, y, z` with `(x, y), (x, z), (y, z)` all in `T` (for sorted edges, i.e.
    `T` has no triangle). -/
def TriFree (T : List Edge) : Prop :=
  ∀ x y z : Nat, (x, y) ∈ T → (x, z) ∈ T → (y, z) ∈ T → False

/-- **(H4)** Euler's bound, for the subgraph of a planar edge list `S` on any `w ≥ 3` vertices. -/
def EulerHyp (planar : List Edge → Prop) : Prop :=
  ∀ S : List Edge, planar S → S.Nodup → (∀ e ∈ S, e.1 < e.2) →
    ∀ W : List Nat, W.Nodup → 3 ≤ W.length →
      (S.filter (inside W)).length ≤ 3 * W.length - 6

/-- **(H5)** Euler's bound for triangle-free subgraphs of a planar edge list `S`. -/
def TriFreeHyp (planar : List Edge → Prop) : Prop :=
  ∀ S : List Edge, planar S → S.Nodup → (∀ e ∈ S, e.1 < e.2) →
    ∀ W : List Nat, W.Nodup → 3 ≤ W.length →
      ∀ T : List Edge, T.Nodup → (∀ e ∈ T, e ∈ S ∧ inside W e = true) → TriFree T →
        T.length ≤ 2 * W.length - 4

/-! ## Certificates (data; checked, not trusted) -/

/-- A certificate for one class representative: an Euler witness `W`, a triangle-free witness
    `(W, T)`, or an isomorphism `π` onto the `i`-th certified A4 graph. -/
inductive Cert where
  | euler (W : List Nat)
  | tf (W : List Nat) (T : List Edge)
  | iso (i : Nat) (π : List Nat)
deriving Repr, Inhabited

end Biplanar.Enum
