import LRATCatcher.Reflect
import LRATCatcher.Cover

/-!
# Biplanar.Basic — definitions for machine-checked non-biplanarity

Earth-Moon project, milestone `lean-verification` (Stage 1, conditional
theorem). Everything a reader must audit to understand the final statement
lives in this file:

* `Graph`, `part`, `Biplanar` — a graph is an explicit edge list over the
  vertices `0..n-1`; a 2-partition is a function `σ : Nat → Bool` on edge
  indices; `Biplanar planar G` says both parts satisfy an abstract predicate
  `planar : List Edge → Prop`.
* `KurCert.valid` — an explicit certificate that an edge set contains a
  subdivision of K₅ or K₃,₃: branch vertices plus one internally
  vertex-disjoint path per branch pair, checked edge by edge. This is the
  *definition* of "contains a Kuratowski subdivision", so hypothesis (H2)
  of the main theorem ("valid certificate ⇒ not planar") is the elementary
  direction of Kuratowski's theorem.
* The CNF encoding `mkCNF G ws`: edge `i` is variable `i` (`true` = part 2);
  the unit clause `¬x₀` (part-swap symmetry); two Sinz sequential counters
  (`atMostSeq`) enforcing `≤ 3n − 6` edges per part (hypothesis (H1) is
  Euler's bound); and one clause per *witness* `w` — "not all edges of
  `w.idx` in part `w.pol`" — justified by its certificate `w.cert`.
  Witnesses are the pre-seeded K₅/K₃,₃ splits and the Kuratowski clauses a
  planarity propagator emitted during the SAT search; the search itself is
  untrusted, only `Witness.ok` and the LRAT certificate of `mkCNF G ws` are.

`Biplanar.Lift` proves: `graphOK G`, `∀ w ∈ ws, Witness.ok G w`,
`(mkCNF G ws).Unsat`, (H1), (H2) ⊢ `¬ Biplanar planar G`.
-/

open Std.Sat

namespace Biplanar

/-- An undirected edge as a pair of vertex numbers. -/
abbrev Edge := Nat × Nat

/-- A finite simple graph: vertices `0..n-1`, explicit edge list. -/
structure Graph where
  n : Nat
  edges : List Edge
deriving Repr, DecidableEq

/-- Sort a pair (edges are stored with `u < v`). -/
def normEdge (e : Edge) : Edge := if e.1 ≤ e.2 then e else (e.2, e.1)

/-- Well-formed instance: `n ≥ 3`, edges are sorted pairs of vertices below
    `n`, no duplicate edges, at least one edge. -/
def graphOK (G : Graph) : Bool :=
  decide (3 ≤ G.n) &&
  G.edges.all (fun e => decide (e.1 < e.2) && decide (e.2 < G.n)) &&
  decide G.edges.Nodup &&
  decide (0 < G.edges.length)

/-- Euler's bound on the number of edges of a planar graph on `n` vertices. -/
def cap (G : Graph) : Nat := 3 * G.n - 6

/-! ## Partitions -/

/-- The edges of `es` (indexed from `i0`) that `σ` sends to side `b`,
    in list order. -/
def partFrom (σ : Nat → Bool) (b : Bool) : Nat → List Edge → List Edge
  | _, [] => []
  | i, e :: es =>
    if σ i = b then e :: partFrom σ b (i + 1) es else partFrom σ b (i + 1) es

/-- Side `b` of the partition `σ` of `G`. -/
def part (G : Graph) (σ : Nat → Bool) (b : Bool) : List Edge :=
  partFrom σ b 0 G.edges

/-- `G` is biplanar relative to an abstract planarity predicate. -/
def Biplanar (planar : List Edge → Prop) (G : Graph) : Prop :=
  ∃ σ : Nat → Bool, planar (part G σ false) ∧ planar (part G σ true)

/-- Number of indices `i0 ≤ i < i0 + len` with `σ i = b`. -/
def cntFrom (σ : Nat → Bool) (b : Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | i0, len + 1 => (if σ i0 = b then 1 else 0) + cntFrom σ b (i0 + 1) len

/-- Number of indices `i < len` with `σ i = b`. -/
def cnt (σ : Nat → Bool) (b : Bool) (len : Nat) : Nat := cntFrom σ b 0 len

/-! ## Kuratowski certificates -/

/-- A subdivision certificate. For `isK5` the branch list has 5 vertices and
    `paths` has 10 entries, one per pair `(bᵢ, bⱼ)`, `i < j`, in the order of
    `pairsK5`; otherwise the branch list is `[a₀, a₁, a₂, b₀, b₁, b₂]` (the
    two sides of K₃,₃) and `paths` has 9 entries in the order of `pairsK33`. -/
structure KurCert where
  isK5 : Bool
  branch : List Nat
  paths : List (List Nat)
deriving Repr, DecidableEq

def pairsK5 : List Nat → List (Nat × Nat)
  | [b0, b1, b2, b3, b4] =>
    [(b0, b1), (b0, b2), (b0, b3), (b0, b4), (b1, b2), (b1, b3), (b1, b4),
     (b2, b3), (b2, b4), (b3, b4)]
  | _ => []

def pairsK33 : List Nat → List (Nat × Nat)
  | [a0, a1, a2, b0, b1, b2] =>
    [(a0, b0), (a0, b1), (a0, b2), (a1, b0), (a1, b1), (a1, b2), (a2, b0),
     (a2, b1), (a2, b2)]
  | _ => []

def KurCert.pairs (c : KurCert) : List (Nat × Nat) :=
  if c.isK5 then pairsK5 c.branch else pairsK33 c.branch

/-- Consecutive vertices of the walk are edges of `E` (in either
    orientation). -/
def chainOK (E : List Edge) : List Nat → Bool
  | u :: v :: rest => E.contains (normEdge (u, v)) && chainOK E (v :: rest)
  | _ => true

/-- The vertices of a path other than its two endpoints. -/
def internals (p : List Nat) : List Nat := (p.drop 1).dropLast

/-- `p` is a path of `E` from `s` to `t`: at least two vertices, no repeated
    vertex, every step an edge of `E`, no branch vertex in its interior. -/
def pathOK (E : List Edge) (branch : List Nat) (s t : Nat) (p : List Nat) : Bool :=
  decide (2 ≤ p.length) && (p.head? == some s) && (p.getLast? == some t) &&
  decide p.Nodup && chainOK E p && (internals p).all (fun v => !branch.contains v)

/-- The certificate exhibits a subdivision of K₅ (resp. K₃,₃) inside the
    edge set `E`: distinct branch vertices, one path per branch pair, and
    pairwise disjoint path interiors. -/
def KurCert.valid (c : KurCert) (E : List Edge) : Bool :=
  let pr := c.pairs
  (if c.isK5 then c.branch.length == 5 else c.branch.length == 6) &&
  decide c.branch.Nodup &&
  (c.paths.length == pr.length) &&
  (pr.zip c.paths).all (fun x => pathOK E c.branch x.1.1 x.1.2 x.2) &&
  decide (c.paths.flatMap internals).Nodup

/-! ## Witnesses (Kuratowski clauses) -/

/-- A dumped clause: "not all edges with indices `idx` lie in part `pol`",
    justified by a certificate over those edges. -/
structure Witness where
  pol : Bool
  idx : List Nat
  cert : KurCert
deriving Repr, DecidableEq

/-- Edge with index `i` (a dummy for out-of-range indices, which
    `Witness.ok` rules out). -/
def edgeOf (G : Graph) (i : Nat) : Edge := G.edges.getD i (0, 0)

/-- The clause of a witness. `pol = true` forbids "all in part 2"
    (literals `(i, false)`), `pol = false` forbids "all in part 1". -/
def Witness.clause (w : Witness) : CNF.Clause Nat :=
  w.idx.map (fun i => (i, !w.pol))

/-- The witness is sound: indices in range and a valid certificate over
    exactly the clause's edges. -/
def Witness.ok (G : Graph) (w : Witness) : Bool :=
  w.idx.all (fun i => decide (i < G.edges.length)) &&
  w.cert.valid (w.idx.map (edgeOf G))

/-! ## Sequential counter (Sinz) -/

/-- Register variable `s(i, j)` ("at least `j+1` of the first `i+1`
    literals are true"), `i < m`, `j < k`, laid out from `base`. -/
def reg (base k i j : Nat) : Nat := base + i * k + j

/-- Sinz's sequential-counter encoding of "at most `k` of the literals
    `(0, pol), …, (m-1, pol)` are true", registers starting at `base`.
    Requires `1 ≤ k`. -/
def atMostSeq (pol : Bool) (m k base : Nat) : List (CNF.Clause Nat) :=
  ((List.range k).filterMap fun j =>
      if j = 0 then none else some [(reg base k 0 j, false)]) ++
  ((List.range m).flatMap fun i =>
    ([(i, !pol), (reg base k i 0, true)] ::
      (if i = 0 then [] else
        ([(i, !pol), (reg base k (i - 1) (k - 1), false)] ::
          (((List.range k).map fun j =>
              [(reg base k (i - 1) j, false), (reg base k i j, true)]) ++
           ((List.range k).filterMap fun j =>
              if j = 0 then none else
                some [(i, !pol), (reg base k (i - 1) (j - 1), false),
                      (reg base k i j, true)]))))))

/-! ## The formula -/

/-- Base clauses: part-swap unit, then the two cardinality counters
    (part 2 registers from `m`, part 1 registers from `m + m·k`). -/
def baseClauses (G : Graph) : List (CNF.Clause Nat) :=
  let m := G.edges.length
  let k := cap G
  [(0, false)] :: (atMostSeq true m k m ++ atMostSeq false m k (m + m * k))

/-- The certified formula: base clauses followed by the witness clauses. -/
def mkCNF (G : Graph) (ws : List Witness) : CNF Nat :=
  { clauses := (baseClauses G ++ ws.map Witness.clause).toArray }

/-- The counter-free formula: part-swap unit and witness clauses only. When a
    refutation's core uses no cardinality clause (as the LRAT core of the
    K₉-core control shows), this formula is UNSAT too, and the resulting
    theorem needs hypothesis (H2) alone — Euler's bound (H1) drops out. -/
def mkCNF₀ (G : Graph) (ws : List Witness) : CNF Nat :=
  { clauses := ([(0, false)] :: ws.map Witness.clause).toArray }

/-- The canonical valuation induced by a partition `σ`: edge variables
    copy `σ`, register variables hold the prefix counts. -/
def val (G : Graph) (σ : Nat → Bool) (v : Nat) : Bool :=
  let m := G.edges.length
  let k := cap G
  if v < m then σ v
  else if v < m + m * k then
    decide ((v - m) % k + 1 ≤ cnt σ true ((v - m) / k + 1))
  else if v < m + m * k + m * k then
    decide ((v - (m + m * k)) % k + 1 ≤ cnt σ false ((v - (m + m * k)) / k + 1))
  else false

/-! ## Witness file parser

Line format (all tokens natural numbers, produced by
`verifier/kuratowski_cert.py::cert_to_lean_line`):

    pol nE e₁ … e_nE kind nB b₁ … b_nB nP (len v₁ … v_len)*

`kind` is `5` for K₅ and `33` for K₃,₃. The parser is NOT part of the
trusted base: a mis-parse can only yield witnesses that fail `Witness.ok`
or a formula whose certificate fails to check. -/

def takeN : Nat → List Nat → Option (List Nat × List Nat)
  | 0, rest => some ([], rest)
  | _ + 1, [] => none
  | n + 1, x :: rest => do
    let (xs, r) ← takeN n rest
    return (x :: xs, r)

def takePaths : Nat → List Nat → Option (List (List Nat) × List Nat)
  | 0, rest => some ([], rest)
  | _ + 1, [] => none
  | n + 1, len :: rest => do
    let (p, r) ← takeN len rest
    let (ps, r') ← takePaths n r
    return (p :: ps, r')

def parseLine (toks : List Nat) : Option Witness := do
  let pol :: nE :: rest := toks | none
  let (idx, rest) ← takeN nE rest
  let kind :: nB :: rest := rest | none
  let (branch, rest) ← takeN nB rest
  let nP :: rest := rest | none
  let (paths, rest) ← takePaths nP rest
  if rest.isEmpty then
    some { pol := pol == 1, idx := idx,
           cert := { isK5 := kind == 5, branch := branch, paths := paths } }
  else
    none

def lineTokens (line : String) : List Nat :=
  (line.splitOn " ").filterMap fun t => if t.isEmpty then none else t.toNat?

def parseWitnesses (s : String) : List Witness :=
  (s.splitOn "\n").filterMap fun line =>
    if line.trimAscii.isEmpty then none else parseLine (lineTokens line)

end Biplanar
