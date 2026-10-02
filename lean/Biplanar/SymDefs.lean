import Biplanar.Basic

/-!
# Biplanar.SymDefs — symmetry-breaking definitions (Stage 2 trusted surface)

Stage 1 (`Biplanar.Basic` + `Biplanar.Lift`) can only lift refutations of
formulas whose every clause is implied by biplanarity. Lex symmetry-breaking
clauses are *not* implied by biplanarity — they hold only for the
lex-minimal member of each orbit — so a sym-on solver run was refused
downstream. This file adds the data and the encoding needed to certify
sym-on runs; `Biplanar.Sym` proves them sound, at the price of one further
hypothesis on `planar`:

* **(H3)** `IsoInvariant`: planarity is a graph-isomorphism invariant — two
  edge lists on the vertices `0..n-1` with the same edge set up to a
  relabelling of the vertices are both `planar` or both not.

Everything a reader must audit to understand the symmetry-broken statement
lives here (as `Biplanar/Basic.lean` does for Stage 1):

* `Gen` — one automorphism generator: a vertex permutation `vperm` and the
  induced permutation `eperm` of the edge *indices*. `Gen.ok` checks by
  decidable computation that `vperm` is a bijection of `0..n-1`, that
  `eperm` maps the edge indices onto themselves, and that the two agree:
  the edge with index `eperm i` is the `vperm`-image of the edge with
  index `i`. Nothing about the generators is assumed; a generator that is
  not an automorphism of `G` fails `Gen.ok`.
* `lexClauses` — the CNF of `x ≤lex (x ∘ eperm)` with the standard
  activity chain (the clause set pysat's `lex_leq` produces in
  `verifier/biplanar_sat.py`): `a₀`, `aᵢ → (xᵢ → yᵢ)`,
  `aᵢ ∧ (xᵢ = yᵢ) → aᵢ₊₁`, where `yᵢ = x_{eperm i}`.
* `mkCNFSym` / `mkCNFSym₀` — the base formula of `Biplanar.Basic` plus one
  lex block per generator (with, resp. without, the cardinality counters).
* `valSym` — the canonical valuation: edge variables and counter registers
  as in `val`, activity variables by their intended meaning `prefEq`.
-/

open Std.Sat

namespace Biplanar

/-! ## Automorphism generators -/

/-- One generator of the symmetry group used for lex symmetry breaking:
    a permutation of the vertices together with the induced permutation of
    the edge indices. Both are plain data, checked by `Gen.ok`. -/
structure Gen where
  vperm : List Nat
  eperm : List Nat
deriving Repr, DecidableEq

/-- Relabel an edge by a vertex permutation given as a list (`getD` keeps
    out-of-range vertices fixed; `permOK` rules those out for real data). -/
def applyPerm (π : List Nat) (e : Edge) : Edge :=
  normEdge (π.getD e.1 e.1, π.getD e.2 e.2)

/-- `π` is a permutation of `0..n-1`: a duplicate-free list of `n` vertices
    below `n`. -/
def permOK (n : Nat) (π : List Nat) : Bool :=
  (π.length == n) && π.all (fun v => decide (v < n)) && decide π.Nodup

/-- The generator's data is consistent with `G`: `vperm` permutes the
    vertices, `eperm` maps edge indices to edge indices and is onto (hence a
    bijection), and edge `eperm i` is the `vperm`-image of edge `i` — i.e.
    `vperm` is an automorphism of `G` and `eperm` is the induced map. -/
def Gen.ok (G : Graph) (g : Gen) : Bool :=
  permOK G.n g.vperm &&
  -- `eperm` must BE a list of the right length, not merely behave like one
  -- through `getD`'s default: without this, `eperm = []` passes for an
  -- identity vertex map, and a downstream consumer reading the raw list as
  -- a permutation array would be wrong. (adversarial audit 2026-09-05, attack 1.)
  (g.eperm.length == G.edges.length) &&
  (List.range G.edges.length).all (fun i =>
    decide (g.eperm.getD i i < G.edges.length)) &&
  (List.range G.edges.length).all (fun j =>
    (List.range G.edges.length).any (fun i => g.eperm.getD i i == j)) &&
  (List.range G.edges.length).all (fun i =>
    edgeOf G (g.eperm.getD i i) == applyPerm g.vperm (edgeOf G i))

/- Note on (H1), recorded from the same audit (attack 10): Euler's bound
    `S.length ≤ 3 * G.n - 6` is a fact about ordinary planarity only for
    `3 ≤ G.n` — at `n = 2` truncated subtraction makes the right-hand side
    `0` while a single edge is planar. Every theorem that assumes (H1) also
    assumes `graphOK G`, which forces `3 ≤ G.n`, so the hypothesis is only
    ever applied inside its domain of validity. The counter-free theorems
    do not assume (H1) at all. -/

/-- **(H3)** Planarity is a graph-isomorphism invariant: relabelling the
    vertices by a permutation of `0..n-1` and reordering the edge list
    changes nothing. The third elementary fact about `planar`, alongside
    (H1) Euler's bound and (H2) Kuratowski's elementary direction. -/
def IsoInvariant (G : Graph) (planar : List Edge → Prop) : Prop :=
  ∀ (π : List Nat) (S T : List Edge), permOK G.n π = true →
    S.Nodup → T.Nodup →
    (∀ e ∈ S, e.1 < e.2 ∧ e.2 < G.n) → (∀ e ∈ T, e.1 < e.2 ∧ e.2 < G.n) →
    (∀ e, e ∈ T ↔ e ∈ S.map (applyPerm π)) → (planar S ↔ planar T)

/-! ## The lex encoding -/

/-- The intended meaning of the activity variable `aᵢ` of a lex block: the
    first `i` edge variables agree with their images under `ep`. -/
def prefEq (σ : Nat → Bool) (ep : List Nat) (i : Nat) : Bool :=
  (List.range i).all (fun s => σ s == σ (ep.getD s s))

/-- CNF of `x ≤lex (x ∘ ep)` on the edge variables `0..m-1`, with the
    activity chain in the variables `base, …, base + m - 1`:
    `a₀`; `aᵢ → (xᵢ → yᵢ)`; `aᵢ ∧ (xᵢ = yᵢ) → aᵢ₊₁`, with `yᵢ = x_{ep i}`.
    Same clause set as `lex_leq` in `verifier/biplanar_sat.py`, except that
    the tautological clause at a position `ep i = i` (where `yᵢ` *is* `xᵢ`)

    **Side conditions (adversarial audit 2026-09-05, attack 6).** This is the CNF
    of the lex inequality only when the activity variables are FRESH,
    `G.edges.length ≤ base`, and the images `ep.getD i i` are below `m`.
    Without freshness the block can alias an edge variable and constrain it:
    with `m = 1`, `base = 0`, `ep = [0]` the block is the positive unit on
    variable 0, which forbids `σ 0 = false` although the lex inequality is
    vacuously true there. Every use here satisfies freshness — `mkCNFSym₀`
    starts activities at `m`, `mkCNFSym` after both counter blocks, and
    `lexAll` advances by `m` per block — and `lexClauses_sat` carries the
    image condition as `hep`, so nothing downstream is affected.
    is omitted: Lean's verified LRAT checker drops tautological clauses when
    it converts a `CNF` to its internal form (`CNF.convertLRAT'` filters out
    the `none`s of `DefaultClause.ofArray`), which would shift every later
    clause id and invalidate the certificate's hints. -/
def lexClauses (m base : Nat) (ep : List Nat) : List (CNF.Clause Nat) :=
  [(base, true)] ::
  (List.range m).flatMap (fun i =>
    (if ep.getD i i = i then ([] : List (CNF.Clause Nat))
     else [[(base + i, false), (i, false), (ep.getD i i, true)]]) ++
      (if i + 1 < m then
        [[(base + i, false), (i, true), (ep.getD i i, true), (base + (i + 1), true)],
         [(base + i, false), (i, false), (ep.getD i i, false), (base + (i + 1), true)]]
       else []))

/-- No clause of `F` contains a literal and its negation. Lean's verified
    LRAT checker silently DROPS such clauses while converting the formula,
    renumbering everything after them, so a certificate for `F.dimacs` would
    not check against `F`. The exporter refuses to write a formula that
    fails this. -/
def clauseNoTaut (c : CNF.Clause Nat) : Bool :=
  c.all (fun l => !c.contains (l.1, !l.2))

def noTautologies (F : CNF Nat) : Bool := F.clauses.all clauseNoTaut

/-- One lex block per generator: block `t` uses the activity variables
    `base + t·m … base + t·m + m - 1`. -/
def lexAll (m : Nat) : Nat → List Gen → List (CNF.Clause Nat)
  | _, [] => []
  | base, g :: gs => lexClauses m base g.eperm ++ lexAll m (base + m) gs

/-- `σ` violates no lex constraint: for no generator is there a position `i`
    with all earlier edge variables equal to their images, `σ i = true` and
    the image variable false. -/
def lexOK (G : Graph) (gens : List Gen) (σ : Nat → Bool) : Bool :=
  gens.all (fun g => (List.range G.edges.length).all (fun i =>
    !(prefEq σ g.eperm i && σ i && !(σ (g.eperm.getD i i)))))

/-- First variable after the edge variables and both counter blocks. -/
def actBase (G : Graph) : Nat :=
  G.edges.length + G.edges.length * cap G + G.edges.length * cap G

/-- The canonical valuation of a symmetry-broken formula whose activity
    variables start at `base`: below `base` as in `val` (edge variables and
    counter registers), above it the intended meaning of the activity
    variables. -/
def valSym (G : Graph) (gens : List Gen) (base : Nat) (σ : Nat → Bool)
    (v : Nat) : Bool :=
  if v < base then val G σ v
  else
    match gens[(v - base) / G.edges.length]? with
    | none => false
    | some g => prefEq σ g.eperm ((v - base) % G.edges.length)

/-- The symmetry-broken formula: base clauses (part-swap unit and the two
    cardinality counters), one lex block per generator, witness clauses. -/
def mkCNFSym (G : Graph) (ws : List Witness) (gens : List Gen) : CNF Nat :=
  { clauses := (baseClauses G ++ lexAll G.edges.length (actBase G) gens
      ++ ws.map Witness.clause).toArray }

/-- Counter-free symmetry-broken formula (activity variables start right
    after the edge variables). -/
def mkCNFSym₀ (G : Graph) (ws : List Witness) (gens : List Gen) : CNF Nat :=
  { clauses := ([(0, false)] :: (lexAll G.edges.length G.edges.length gens
      ++ ws.map Witness.clause)).toArray }

end Biplanar
