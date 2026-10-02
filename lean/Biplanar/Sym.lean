import Biplanar.SymDefs
import Biplanar.Lift

/-!
# Biplanar.Sym — soundness of lex symmetry breaking ("Stage 2")

The Stage-1 Lift lemma needs every clause of the formula to be satisfied by
*every* biplanar partition. Lex clauses are not: they hold only for the
lex-minimal member of an orbit. What is true — and what this file proves —
is that if `G` has any biplanar partition, then it has one that satisfies
all of them:

* `descend` — a `Nat`-valued rank (`code`, the first `m` bits of `σ` read as
  a binary number, most significant first) makes the orbit descent
  terminate;
* one descent step replaces `σ` by `σ ∘ eperm` (a generator) or by its
  pointwise negation (the part swap) whenever that lowers the rank; both
  moves preserve "both parts planar" — the generator move by (H3) and
  `part_gen_mem`, the swap trivially;
* at a minimum, `σ 0 = false` and no lex constraint is violated
  (`lexOK`), so the canonical valuation `valSym` satisfies the unit clause,
  the counters, the witness clauses (Stage 1) *and* every lex clause
  (`lexClauses_sat`).

Hence `not_biplanar_of_unsat_sym` / `not_biplanar_of_unsat_sym₀`: a
refutation of the symmetry-broken formula gives `¬ Biplanar planar G` for
every `planar` satisfying (H1), (H2), (H3) — respectively (H2), (H3).
-/

open Std.Sat

namespace Biplanar

/-! ## Four-literal clauses -/

theorem eval4 (α : Nat → Bool) (a : Nat) (pa : Bool) (b : Nat) (pb : Bool)
    (c : Nat) (pc : Bool) (d : Nat) (pd : Bool) :
    CNF.Clause.eval α [(a, pa), (b, pb), (c, pc), (d, pd)] =
      ((α a == pa) || (α b == pb) || (α c == pc) || (α d == pd)) := by
  simp [CNF.Clause.eval, Bool.or_assoc]

/-! ## The activity predicate -/

theorem prefEq_zero (σ : Nat → Bool) (ep : List Nat) : prefEq σ ep 0 = true := rfl

theorem prefEq_succ (σ : Nat → Bool) (ep : List Nat) (i : Nat) :
    prefEq σ ep (i + 1) = (prefEq σ ep i && (σ i == σ (ep.getD i i))) := by
  simp [prefEq, List.range_succ]

theorem prefEq_spec {σ : Nat → Bool} {ep : List Nat} {i : Nat} :
    prefEq σ ep i = true ↔ ∀ s, s < i → σ s = σ (ep.getD s s) := by
  simp [prefEq]

/-! ## The rank: the first `m` bits of `σ` as a binary number -/

/-- `σ (i0), …, σ (i0+len-1)` read as a `len`-bit number, most significant
    bit first. -/
def codeFrom (σ : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | i0, len + 1 => (if σ i0 then 2 ^ len else 0) + codeFrom σ (i0 + 1) len

/-- The rank of a partition: its first `m` bits as a binary number. -/
def code (m : Nat) (σ : Nat → Bool) : Nat := codeFrom σ 0 m

theorem codeFrom_lt (σ : Nat → Bool) : ∀ i0 len, codeFrom σ i0 len < 2 ^ len
  | _, 0 => by simp [codeFrom]
  | i0, len + 1 => by
    have ih := codeFrom_lt σ (i0 + 1) len
    have hsplit : (if σ i0 then 2 ^ len else 0) ≤ 2 ^ len := by
      split <;> omega
    have h2 : (2:Nat) ^ (len + 1) = 2 ^ len + 2 ^ len := Nat.two_pow_succ len
    simp only [codeFrom]
    omega

/-- Rank order refines the lexicographic order: if `σ` ranks no higher than
    `τ` then at the first position where they differ, `σ` has the `false`. -/
theorem lex_of_codeFrom_le (σ τ : Nat → Bool) (len : Nat) :
    ∀ (i0 t : Nat), codeFrom σ i0 len ≤ codeFrom τ i0 len → t < len →
      (∀ s, s < t → σ (i0 + s) = τ (i0 + s)) → σ (i0 + t) = true →
      τ (i0 + t) = true := by
  induction len with
  | zero => intro i0 t _ ht _ _; exact absurd ht (Nat.not_lt_zero t)
  | succ len ih =>
    intro i0 t hle ht hagree hσ
    cases t with
    | zero =>
      simp only [Nat.add_zero] at hσ ⊢
      cases hτ : τ i0 with
      | true => rfl
      | false =>
        exfalso
        have h2 := codeFrom_lt τ (i0 + 1) len
        have e1 : (if σ i0 then (2:Nat) ^ len else 0) = 2 ^ len := by rw [hσ]; simp
        have e2 : (if τ i0 then (2:Nat) ^ len else 0) = 0 := by rw [hτ]; simp
        simp only [codeFrom, e1, e2] at hle
        omega
    | succ t =>
      have h0 : σ i0 = τ i0 := by
        have h := hagree 0 (Nat.succ_pos t)
        simpa using h
      have hle' : codeFrom σ (i0 + 1) len ≤ codeFrom τ (i0 + 1) len := by
        simp only [codeFrom, h0] at hle
        omega
      have hidx : ∀ s : Nat, i0 + (s + 1) = i0 + 1 + s := fun s => by omega
      rw [hidx t] at hσ ⊢
      refine ih (i0 + 1) t hle' (Nat.lt_of_succ_lt_succ ht) ?_ hσ
      intro s hs
      have h := hagree (s + 1) (Nat.succ_lt_succ hs)
      rwa [hidx s] at h

/-- A lex violation strictly lowers the rank. -/
theorem code_lt_of_violation (m : Nat) (σ τ : Nat → Bool) (t : Nat) (ht : t < m)
    (hagree : ∀ s, s < t → σ s = τ s) (hσ : σ t = true) (hτ : τ t = false) :
    code m τ < code m σ := by
  rcases Nat.lt_or_ge (code m τ) (code m σ) with h | h
  · exact h
  exfalso
  have hle : codeFrom σ 0 m ≤ codeFrom τ 0 m := h
  have hagree' : ∀ s, s < t → σ (0 + s) = τ (0 + s) := by
    intro s hs; simpa using hagree s hs
  have hσ' : σ (0 + t) = true := by simpa using hσ
  have := lex_of_codeFrom_le σ τ m 0 t hle ht hagree' hσ'
  rw [Nat.zero_add, hτ] at this
  exact Bool.noConfusion this

/-- The part swap lowers the rank when edge 0 is in part 2. -/
theorem code_swap_lt (m : Nat) (σ : Nat → Bool) (hm : 0 < m) (h0 : σ 0 = true) :
    code m (fun i => !σ i) < code m σ :=
  code_lt_of_violation m σ (fun i => !σ i) 0 hm
    (fun s hs => absurd hs (Nat.not_lt_zero s)) h0 (by simp [h0])

/-! ## Descent -/

/-- Any property `P` preserved by rank-lowering moves is realised at a
    position where no move applies. -/
theorem descend (m : Nat) (P Q : (Nat → Bool) → Prop)
    (step : ∀ σ, P σ → ¬ Q σ → ∃ τ, P τ ∧ code m τ < code m σ) :
    ∀ σ, P σ → ∃ τ, P τ ∧ Q τ := by
  have key : ∀ c σ, code m σ ≤ c → P σ → ∃ τ, P τ ∧ Q τ := by
    intro c
    induction c with
    | zero =>
      intro σ hc hP
      by_cases hQ : Q σ
      · exact ⟨σ, hP, hQ⟩
      · obtain ⟨τ, _, hlt⟩ := step σ hP hQ
        exact absurd hlt (by omega)
    | succ c ih =>
      intro σ hc hP
      by_cases hQ : Q σ
      · exact ⟨σ, hP, hQ⟩
      · obtain ⟨τ, hPτ, hlt⟩ := step σ hP hQ
        exact ih τ (by omega) hPτ
  intro σ hP
  exact key (code m σ) σ (Nat.le_refl _) hP

/-! ## Partition membership -/

theorem mem_partFrom (σ : Nat → Bool) (b : Bool) :
    ∀ (i0 : Nat) (es : List Edge) (e : Edge), e ∈ partFrom σ b i0 es →
      ∃ j, j < es.length ∧ σ (i0 + j) = b ∧ es.getD j (0, 0) = e
  | _, [], e, h => by simp [partFrom] at h
  | i0, a :: es, e, h => by
    simp only [partFrom] at h
    split at h
    · next hb =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, by simpa using hb, by simp⟩
      · obtain ⟨j, hj, hσ, hg⟩ := mem_partFrom σ b (i0 + 1) es e h
        refine ⟨j + 1, by simpa using hj, ?_, by simpa using hg⟩
        rw [show i0 + (j + 1) = i0 + 1 + j by omega]; exact hσ
    · obtain ⟨j, hj, hσ, hg⟩ := mem_partFrom σ b (i0 + 1) es e h
      refine ⟨j + 1, by simpa using hj, ?_, by simpa using hg⟩
      rw [show i0 + (j + 1) = i0 + 1 + j by omega]; exact hσ

theorem mem_part {G : Graph} {σ : Nat → Bool} {b : Bool} {e : Edge}
    (h : e ∈ part G σ b) :
    ∃ j, j < G.edges.length ∧ σ j = b ∧ edgeOf G j = e := by
  obtain ⟨j, hj, hσ, hg⟩ := mem_partFrom σ b 0 G.edges e h
  exact ⟨j, hj, by simpa using hσ, hg⟩

/-! ## Generator data -/

theorem Gen.ok_range {G : Graph} {g : Gen} (h : g.ok G = true) :
    ∀ i, i < G.edges.length → g.eperm.getD i i < G.edges.length := by
  simp only [Gen.ok, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact fun i hi => h.1.1.2 i hi

theorem Gen.ok_surj {G : Graph} {g : Gen} (h : g.ok G = true) :
    ∀ j, j < G.edges.length → ∃ i, i < G.edges.length ∧ g.eperm.getD i i = j := by
  simp only [Gen.ok, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range, beq_iff_eq] at h
  intro j hj
  obtain ⟨i, hi, hij⟩ := h.1.2 j hj
  exact ⟨i, hi, hij⟩

theorem Gen.ok_compat {G : Graph} {g : Gen} (h : g.ok G = true) :
    ∀ i, i < G.edges.length →
      edgeOf G (g.eperm.getD i i) = applyPerm g.vperm (edgeOf G i) := by
  simp only [Gen.ok, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact fun i hi => h.2 i hi

theorem Gen.ok_perm {G : Graph} {g : Gen} (h : g.ok G = true) :
    permOK G.n g.vperm = true := by
  simp only [Gen.ok, Bool.and_eq_true] at h
  -- Gen.ok now has five conjuncts (the eperm length check was added after
  -- the 2026-09-05 audit), nesting as ((((A ∧ B) ∧ C) ∧ D) ∧ E)
  exact h.1.1.1.1

/-- The generator move relabels the parts: side `b` of `σ` is exactly the
    `vperm`-image of side `b` of `σ ∘ eperm`. -/
theorem part_gen_mem (G : Graph) (g : Gen) (σ : Nat → Bool) (b : Bool)
    (hg : g.ok G = true) (e : Edge) :
    e ∈ part G σ b ↔
      e ∈ (part G (fun j => σ (g.eperm.getD j j)) b).map (applyPerm g.vperm) := by
  constructor
  · intro he
    obtain ⟨j, hj, hσ, hgj⟩ := mem_part he
    obtain ⟨i, hi, hij⟩ := Gen.ok_surj hg j hj
    refine List.mem_map.mpr ⟨edgeOf G i, ?_, ?_⟩
    · exact edgeOf_mem_part G _ hi (by rw [hij]; exact hσ)
    · rw [← Gen.ok_compat hg i hi, hij, hgj]
  · intro he
    obtain ⟨e', he', hmap⟩ := List.mem_map.mp he
    obtain ⟨i, hi, hσ, hgi⟩ := mem_part he'
    have hlt := Gen.ok_range hg i hi
    have : edgeOf G (g.eperm.getD i i) ∈ part G σ b :=
      edgeOf_mem_part G σ hlt hσ
    rw [Gen.ok_compat hg i hi, hgi, hmap] at this
    exact this

/-! ## Soundness of one lex block -/

theorem lexClauses_sat (m base : Nat) (ep : List Nat) (α σ : Nat → Bool)
    (hm : 0 < m)
    (hep : ∀ i, i < m → ep.getD i i < m)
    (hlit : ∀ i, i < m → α i = σ i)
    (hact : ∀ i, i < m → α (base + i) = prefEq σ ep i)
    (hlex : ∀ i, i < m → prefEq σ ep i = true → σ i = true →
      σ (ep.getD i i) = true) :
    ∀ cl ∈ lexClauses m base ep, CNF.Clause.eval α cl = true := by
  intro cl hcl
  simp only [lexClauses] at hcl
  rw [List.mem_cons] at hcl
  rcases hcl with rfl | hcl
  · -- a₀
    have h0 := hact 0 hm
    rw [Nat.add_zero] at h0
    rw [eval1, h0, prefEq_zero]
    rfl
  · rw [List.mem_flatMap] at hcl
    obtain ⟨i, hir, hci⟩ := hcl
    rw [List.mem_range] at hir
    have hi : i < m := hir
    have hy : ep.getD i i < m := hep i hi
    have hai := hact i hi
    rw [List.mem_append] at hci
    rcases hci with hci | hci
    · -- aᵢ → (xᵢ → yᵢ); omitted when `ep i = i` (there it is a tautology)
      split at hci
      · simp at hci
      rw [List.mem_cons] at hci
      rcases hci with rfl | hci
      · rw [eval3, hai, hlit i hi, hlit _ hy]
        by_cases ha : prefEq σ ep i = true
        · by_cases hx : σ i = true
          · rw [hlex i hi ha hx]; simp
          · have : σ i = false := by cases h : σ i <;> simp_all
            simp [this]
        · have : prefEq σ ep i = false := by
            cases h : prefEq σ ep i <;> simp_all
          simp [this]
      · simp at hci
    · split at hci
      · next hlt =>
        have hai1 := hact (i + 1) hlt
        rw [List.mem_cons, List.mem_cons] at hci
        rcases hci with rfl | rfl | hci
        · -- aᵢ ∧ ¬xᵢ ∧ ¬yᵢ → aᵢ₊₁
          rw [eval4, hai, hai1, hlit i hi, hlit _ hy]
          by_cases ha : prefEq σ ep i = true
          · by_cases hx : σ i = true
            · simp [hx]
            · have hx' : σ i = false := by cases h : σ i <;> simp_all
              by_cases hy2 : σ (ep.getD i i) = true
              · rw [hy2]; simp
              · have hy' : σ (ep.getD i i) = false := by
                  cases h : σ (ep.getD i i) <;> simp_all
                rw [prefEq_succ, ha, hx', hy']
                simp
          · have : prefEq σ ep i = false := by
              cases h : prefEq σ ep i <;> simp_all
            simp [this]
        · -- aᵢ ∧ xᵢ ∧ yᵢ → aᵢ₊₁
          rw [eval4, hai, hai1, hlit i hi, hlit _ hy]
          by_cases ha : prefEq σ ep i = true
          · by_cases hx : σ i = true
            · by_cases hy2 : σ (ep.getD i i) = true
              · rw [prefEq_succ, ha, hx, hy2]; simp
              · have hy' : σ (ep.getD i i) = false := by
                  cases h : σ (ep.getD i i) <;> simp_all
                rw [hy']; simp
            · have hx' : σ i = false := by cases h : σ i <;> simp_all
              simp [hx']
          · have : prefEq σ ep i = false := by
              cases h : prefEq σ ep i <;> simp_all
            simp [this]
        · simp at hci
      · simp at hci

/-! ## Soundness of all lex blocks -/

theorem lexAll_sat (m : Nat) (α σ : Nat → Bool) (hm : 0 < m)
    (hlit : ∀ i, i < m → α i = σ i) :
    ∀ (gs : List Gen) (base : Nat),
      (∀ t g, gs[t]? = some g → ∀ i, i < m → α (base + t * m + i) = prefEq σ g.eperm i) →
      (∀ g ∈ gs, ∀ i, i < m → g.eperm.getD i i < m) →
      (∀ g ∈ gs, ∀ i, i < m → prefEq σ g.eperm i = true → σ i = true →
        σ (g.eperm.getD i i) = true) →
      ∀ cl ∈ lexAll m base gs, CNF.Clause.eval α cl = true
  | [], base, _, _, _ => by intro cl hcl; simp [lexAll] at hcl
  | g :: gs, base, hact, hep, hlex => by
    intro cl hcl
    simp only [lexAll, List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · refine lexClauses_sat m base g.eperm α σ hm
        (hep g (List.mem_cons_self ..)) hlit ?_
        (hlex g (List.mem_cons_self ..)) cl hcl
      intro i hi
      have := hact 0 g rfl i hi
      simpa using this
    · refine lexAll_sat m α σ hm hlit gs (base + m) ?_ ?_ ?_ cl hcl
      · intro t g' hg' i hi
        have := hact (t + 1) g' (by simpa using hg') i hi
        have heq : base + (t + 1) * m + i = base + m + t * m + i := by
          rw [Nat.succ_mul]; omega
        rwa [heq] at this
      · exact fun g' hg' => hep g' (List.mem_cons_of_mem g hg')
      · exact fun g' hg' => hlex g' (List.mem_cons_of_mem g hg')

/-! ## The canonical valuation -/

theorem valSym_lt (G : Graph) (gens : List Gen) (base : Nat) (σ : Nat → Bool)
    {v : Nat} (hv : v < base) : valSym G gens base σ v = val G σ v := by
  simp [valSym, hv]

theorem valSym_edge (G : Graph) (gens : List Gen) (base : Nat) (σ : Nat → Bool)
    (hb : G.edges.length ≤ base) {i : Nat} (hi : i < G.edges.length) :
    valSym G gens base σ i = σ i := by
  rw [valSym_lt G gens base σ (by omega), val_lt G σ hi]

theorem valSym_act (G : Graph) (gens : List Gen) (base : Nat) (σ : Nat → Bool)
    (hm : 0 < G.edges.length) (t : Nat) (g : Gen) (hg : gens[t]? = some g)
    {i : Nat} (hi : i < G.edges.length) :
    valSym G gens base σ (base + t * G.edges.length + i) = prefEq σ g.eperm i := by
  obtain ⟨hdiv, hmod⟩ := reg_decode (i := t) hm hi
  have hnot : ¬ (base + t * G.edges.length + i < base) := by omega
  have hsub : base + t * G.edges.length + i - base = t * G.edges.length + i := by
    omega
  simp only [valSym, if_neg hnot, hsub, hdiv, hmod, hg]

/-! ## The symmetry-broken Lift lemmas -/

theorem lexOK_spec {G : Graph} {gens : List Gen} {σ : Nat → Bool}
    (h : lexOK G gens σ = true) :
    ∀ g ∈ gens, ∀ i, i < G.edges.length → prefEq σ g.eperm i = true →
      σ i = true → σ (g.eperm.getD i i) = true := by
  simp only [lexOK, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    Bool.and_eq_false_iff] at h
  intro g hg i hi hpe hx
  rcases h g hg i hi with (h3 | h3) | h3
  · exact absurd hpe (by simp [h3])
  · exact absurd hx (by simp [h3])
  · simpa using h3

/-- Lift for the symmetry-broken formula, counter-free variant. -/
theorem eval_mkCNFSym₀ (G : Graph) (ws : List Witness) (gens : List Gen)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hgens : gens.all (Gen.ok G) = true)
    (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (σ : Nat → Bool) (hσ0 : σ 0 = false) (hlex : lexOK G gens σ = true)
    (hp1 : planar (part G σ false)) (hp2 : planar (part G σ true)) :
    (mkCNFSym₀ G ws gens).eval (valSym G gens G.edges.length σ) = true := by
  obtain ⟨_, _, _, hpos⟩ := graphOK_spec hG
  rw [List.all_eq_true] at hws hgens
  have hlit : ∀ i, i < G.edges.length →
      valSym G gens G.edges.length σ i = σ i :=
    fun i hi => valSym_edge G gens _ σ (Nat.le_refl _) hi
  rw [CNF.eval, Array.all_eq_true']
  intro cl hcl
  simp only [mkCNFSym₀, List.mem_toArray, List.mem_cons, List.mem_append,
    List.mem_map] at hcl
  rcases hcl with rfl | hcl | ⟨w, hw, rfl⟩
  · rw [eval1, hlit 0 hpos, hσ0]; rfl
  · refine lexAll_sat G.edges.length _ σ hpos hlit gens G.edges.length ?_ ?_
      (lexOK_spec hlex) cl hcl
    · intro t g hg i hi
      exact valSym_act G gens G.edges.length σ hpos t g hg hi
    · intro g hg i hi
      exact Gen.ok_range (hgens g hg) i hi
  · exact witness_clause_sat G σ _ w (hws w hw) planar H2
      (by cases hp : w.pol <;> simp [hp1, hp2]) hlit

/-- Lift for the symmetry-broken formula, with the cardinality counters. -/
theorem eval_mkCNFSym (G : Graph) (ws : List Witness) (gens : List Gen)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hgens : gens.all (Gen.ok G) = true)
    (planar : List Edge → Prop)
    (H1 : ∀ S : List Edge, S.Nodup → (∀ e ∈ S, e.1 < e.2 ∧ e.2 < G.n) →
      planar S → S.length ≤ 3 * G.n - 6)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (σ : Nat → Bool) (hσ0 : σ 0 = false) (hlex : lexOK G gens σ = true)
    (hp1 : planar (part G σ false)) (hp2 : planar (part G σ true)) :
    (mkCNFSym G ws gens).eval (valSym G gens (actBase G) σ) = true := by
  obtain ⟨h3n, hedges, hnodup, hpos⟩ := graphOK_spec hG
  rw [List.all_eq_true] at hws hgens
  have hk : 1 ≤ cap G := by simp only [cap]; omega
  have hbase : G.edges.length ≤ actBase G := by simp only [actBase]; omega
  have hlit : ∀ i, i < G.edges.length → valSym G gens (actBase G) σ i = σ i :=
    fun i hi => valSym_edge G gens _ σ hbase hi
  have hbound : ∀ b, planar (part G σ b) → cnt σ b G.edges.length ≤ cap G := by
    intro b hp
    have := H1 (part G σ b) (part_nodup G σ b hnodup)
      (fun e he => hedges e (mem_edges_of_mem_part he)) hp
    rw [length_part] at this
    exact this
  have hreg1 : ∀ i j, i < G.edges.length → j < cap G →
      valSym G gens (actBase G) σ (reg G.edges.length (cap G) i j) =
        decide (j + 1 ≤ cnt σ true (i + 1)) := by
    intro i j hi hj
    have hlt : reg G.edges.length (cap G) i j < actBase G := by
      have := reg_lt hi hj
      simp only [reg, actBase]; omega
    rw [valSym_lt G gens _ σ hlt, val_reg_true G σ hk hi hj]
  have hreg2 : ∀ i j, i < G.edges.length → j < cap G →
      valSym G gens (actBase G) σ
        (reg (G.edges.length + G.edges.length * cap G) (cap G) i j) =
        decide (j + 1 ≤ cnt σ false (i + 1)) := by
    intro i j hi hj
    have hlt : reg (G.edges.length + G.edges.length * cap G) (cap G) i j
        < actBase G := by
      have := reg_lt hi hj
      simp only [reg, actBase]; omega
    rw [valSym_lt G gens _ σ hlt, val_reg_false G σ hk hi hj]
  rw [CNF.eval, Array.all_eq_true']
  intro cl hcl
  simp only [mkCNFSym, List.mem_toArray, List.mem_append, baseClauses,
    List.mem_cons, List.mem_map] at hcl
  rcases hcl with ((rfl | hcl | hcl) | hcl) | ⟨w, hw, rfl⟩
  · rw [eval1, hlit 0 hpos, hσ0]; rfl
  · exact atMostSeq_sat true G.edges.length (cap G) G.edges.length _ σ hpos hk
      hlit hreg1 (hbound true hp2) cl hcl
  · exact atMostSeq_sat false G.edges.length (cap G)
      (G.edges.length + G.edges.length * cap G) _ σ hpos hk hlit hreg2
      (hbound false hp1) cl hcl
  · refine lexAll_sat G.edges.length _ σ hpos hlit gens (actBase G) ?_ ?_
      (lexOK_spec hlex) cl hcl
    · intro t g hg i hi
      exact valSym_act G gens (actBase G) σ hpos t g hg hi
    · intro g hg i hi
      exact Gen.ok_range (hgens g hg) i hi
  · exact witness_clause_sat G σ _ w (hws w hw) planar H2
      (by cases hp : w.pol <;> simp [hp1, hp2]) hlit

/-- Reading a lex violation off `lexOK … = false`. -/
theorem lexOK_violation {G : Graph} {gens : List Gen} {σ : Nat → Bool}
    (h : lexOK G gens σ = false) :
    ∃ g ∈ gens, ∃ i, i < G.edges.length ∧ prefEq σ g.eperm i = true ∧
      σ i = true ∧ σ (g.eperm.getD i i) = false := by
  simp only [lexOK, List.all_eq_false] at h
  obtain ⟨g, hg, hgbad⟩ := h
  rw [Bool.not_eq_true, List.all_eq_false] at hgbad
  obtain ⟨i, hi, hbad⟩ := hgbad
  refine ⟨g, hg, i, List.mem_range.mp hi, ?_, ?_, ?_⟩ <;>
    revert hbad <;>
    cases hpe : prefEq σ g.eperm i <;> cases hxx : σ i <;>
      cases hyy : σ (g.eperm.getD i i) <;> simp

/-! ## Orbit descent -/

/-- **The symmetry-breaking soundness lemma.** If `G` has a partition into
    two `planar` parts, it has one with edge 0 in part 1 that violates no
    lex constraint of any checked generator. -/
theorem exists_normalised (G : Graph) (gens : List Gen)
    (hG : graphOK G = true) (hgens : gens.all (Gen.ok G) = true)
    (planar : List Edge → Prop) (H3 : IsoInvariant G planar)
    (σ₀ : Nat → Bool) (hp1 : planar (part G σ₀ false))
    (hp2 : planar (part G σ₀ true)) :
    ∃ σ : Nat → Bool, planar (part G σ false) ∧ planar (part G σ true) ∧
      σ 0 = false ∧ lexOK G gens σ = true := by
  obtain ⟨h3n, hedges, hnodup, hpos⟩ := graphOK_spec hG
  rw [List.all_eq_true] at hgens
  have hrange : ∀ (τ : Nat → Bool) (b : Bool),
      ∀ e ∈ part G τ b, e.1 < e.2 ∧ e.2 < G.n :=
    fun τ b e he => hedges e (mem_edges_of_mem_part he)
  -- a generator move preserves biplanarity
  have hmove : ∀ (g : Gen), g ∈ gens → ∀ (τ : Nat → Bool) (b : Bool),
      planar (part G τ b) →
      planar (part G (fun j => τ (g.eperm.getD j j)) b) := by
    intro g hg τ b hpl
    exact (H3 g.vperm (part G (fun j => τ (g.eperm.getD j j)) b) (part G τ b)
      (Gen.ok_perm (hgens g hg)) (part_nodup G _ b hnodup) (part_nodup G τ b hnodup)
      (hrange _ b) (hrange τ b)
      (fun e => part_gen_mem G g τ b (hgens g hg) e)).mpr hpl
  refine descend G.edges.length
    (fun σ => planar (part G σ false) ∧ planar (part G σ true))
    (fun σ => σ 0 = false ∧ lexOK G gens σ = true) ?_ σ₀ ⟨hp1, hp2⟩
    |>.imp ?_
  · -- the descent step
    intro σ hP hQ
    by_cases h0 : σ 0 = false
    · -- some lex constraint is violated
      have hbad : lexOK G gens σ = false := by
        cases h : lexOK G gens σ
        · rfl
        · exact absurd ⟨h0, h⟩ hQ
      obtain ⟨g, hg, i, hi, hpe, hx, hy⟩ := lexOK_violation hbad
      refine ⟨fun j => σ (g.eperm.getD j j),
        ⟨hmove g hg σ false hP.1, hmove g hg σ true hP.2⟩, ?_⟩
      refine code_lt_of_violation G.edges.length σ _ i hi ?_ hx ?_
      · intro s hs
        exact (prefEq_spec.mp hpe) s hs
      · simpa using hy
    · have h0' : σ 0 = true := by cases h : σ 0 <;> simp_all
      exact ⟨fun i => !σ i,
        ⟨by rw [part_not]; exact hP.2, by rw [part_not]; exact hP.1⟩,
        code_swap_lt G.edges.length σ hpos h0'⟩
  · rintro σ ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩

/-! ## Main theorems -/

/-- **Conditional non-biplanarity from a symmetry-broken refutation
    (counter-free).** Hypotheses (H2) and (H3) only. -/
theorem not_biplanar_of_unsat_sym₀ (G : Graph) (ws : List Witness) (gens : List Gen)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hgens : gens.all (Gen.ok G) = true)
    (hunsat : (mkCNFSym₀ G ws gens).Unsat)
    (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (H3 : IsoInvariant G planar) :
    ¬ Biplanar planar G := by
  intro ⟨σ₀, h1, h2⟩
  obtain ⟨σ, hp1, hp2, hσ0, hlex⟩ :=
    exists_normalised G gens hG hgens planar H3 σ₀ h1 h2
  have := hunsat (valSym G gens G.edges.length σ)
  rw [eval_mkCNFSym₀ G ws gens hG hws hgens planar H2 σ hσ0 hlex hp1 hp2] at this
  exact Bool.noConfusion this

/-- **Conditional non-biplanarity from a symmetry-broken refutation.**
    Hypotheses (H1), (H2), (H3). -/
theorem not_biplanar_of_unsat_sym (G : Graph) (ws : List Witness) (gens : List Gen)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hgens : gens.all (Gen.ok G) = true)
    (hunsat : (mkCNFSym G ws gens).Unsat)
    (planar : List Edge → Prop)
    (H1 : ∀ S : List Edge, S.Nodup → (∀ e ∈ S, e.1 < e.2 ∧ e.2 < G.n) →
      planar S → S.length ≤ 3 * G.n - 6)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (H3 : IsoInvariant G planar) :
    ¬ Biplanar planar G := by
  intro ⟨σ₀, h1, h2⟩
  obtain ⟨σ, hp1, hp2, hσ0, hlex⟩ :=
    exists_normalised G gens hG hgens planar H3 σ₀ h1 h2
  have := hunsat (valSym G gens (actBase G) σ)
  rw [eval_mkCNFSym G ws gens hG hws hgens planar H1 H2 σ hσ0 hlex hp1 hp2] at this
  exact Bool.noConfusion this

/-- **Cube-leaf variant** of the symmetry-broken theorem (counter-free). -/
theorem not_biplanar_on_cube_of_unsat_sym₀ (G : Graph) (ws : List Witness)
    (gens : List Gen) (cube : LRATCatcher.Cube)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hgens : gens.all (Gen.ok G) = true)
    (hunsat : (LRATCatcher.Cube.leafCNF cube (mkCNFSym₀ G ws gens)).Unsat)
    (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ lexOK G gens σ = true ∧
        cube.sat (valSym G gens G.edges.length σ) = true ∧
        planar (part G σ false) ∧ planar (part G σ true) := by
  intro ⟨σ, hσ0, hlex, hcube, hp1, hp2⟩
  have := hunsat (valSym G gens G.edges.length σ)
  simp only [LRATCatcher.Cube.leafCNF, CNF.eval_append,
    LRATCatcher.Cube.eval_toCNF, hcube,
    eval_mkCNFSym₀ G ws gens hG hws hgens planar H2 σ hσ0 hlex hp1 hp2,
    Bool.and_self] at this
  exact Bool.noConfusion this

/-! ## Composition over cubes with INDEPENDENT witness sets

The cube-and-conquer composition LRAT-Catcher provides (`cover_unsat`)
works at the level of one CNF: every leaf must be `cube ++ F` for the
*same* `F`, hence the same witness list. At the scale where a single
witness file no longer fits in memory that is the binding constraint, not
the certificates.

The way out is to compose one level up, over the *statements* rather than
the formulas. `not_biplanar_on_cube_of_unsat_sym₀` produces, for one cube,
a proposition that never mentions `ws` — the cube's satisfaction is tested
against `valSym`, which depends only on `G`, the generators and `σ`. So
each cube may be refuted from its own witness set, with its own formula
and its own certificate, and the pieces still compose. Memory then scales
with the hardest single cube instead of with the whole problem. -/

/-- **Cube composition, independent witness sets.** Given a covering set of
    cubes (certified by `negCubesCNF … .Unsat`) and, for each cube, the
    statement that no normalised biplanar partition agrees with it — each
    of which may come from a different witness set and a different
    certificate — the graph is not biplanar. -/
theorem not_biplanar_of_cover (G : Graph) (gens : List Gen)
    (cubes : List LRATCatcher.Cube)
    (hG : graphOK G = true) (hgens : gens.all (Gen.ok G) = true)
    (planar : List Edge → Prop) (H3 : IsoInvariant G planar)
    (hcover : (LRATCatcher.negCubesCNF cubes).Unsat)
    (hleaves : ∀ c ∈ cubes, ¬ ∃ σ : Nat → Bool, σ 0 = false ∧
      lexOK G gens σ = true ∧
      c.sat (valSym G gens G.edges.length σ) = true ∧
      planar (part G σ false) ∧ planar (part G σ true)) :
    ¬ Biplanar planar G := by
  intro ⟨σ₀, h1, h2⟩
  obtain ⟨σ, hp1, hp2, hσ0, hlex⟩ :=
    exists_normalised G gens hG hgens planar H3 σ₀ h1 h2
  obtain ⟨c, hc, hsat⟩ :=
    LRATCatcher.cover_complete hcover (valSym G gens G.edges.length σ)
  exact hleaves c hc ⟨σ, hσ0, hlex, hsat, hp1, hp2⟩

end Biplanar
