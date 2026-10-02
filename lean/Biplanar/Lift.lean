import Biplanar.Basic

/-!
# Biplanar.Lift — encoding soundness ("Lift" lemma)

Every partition of `G` into two `planar` parts (with edge 0 in part 1)
induces a valuation `val G σ` satisfying every clause of `mkCNF G ws`:

* the unit clause `¬x₀` by the normalisation `σ 0 = false`;
* the two sequential counters because (H1) bounds each part by `3n − 6`
  (`atMostSeq_sat`, a generic soundness lemma for Sinz's encoding);
* each witness clause because its certificate, valid over the clause's
  edges, stays valid over the whole part containing them, and (H2) then
  says that part is not planar (`witness_clause_sat`).

Hence `(mkCNF G ws).Unsat` leaves no biplanar partition
(`not_biplanar_of_unsat`), and a refuted cube leaf leaves none inside the
cube (`not_biplanar_on_cube_of_unsat`).
-/

open Std.Sat

namespace Biplanar

/-! ## Partition lemmas -/

theorem partFrom_sublist (σ : Nat → Bool) (b : Bool) :
    ∀ (i0 : Nat) (es : List Edge), List.Sublist (partFrom σ b i0 es) es
  | _, [] => List.Sublist.slnil
  | i, e :: es => by
    simp only [partFrom]
    split
    · exact List.Sublist.cons_cons e (partFrom_sublist σ b (i + 1) es)
    · exact List.Sublist.cons e (partFrom_sublist σ b (i + 1) es)

theorem part_sublist (G : Graph) (σ : Nat → Bool) (b : Bool) :
    List.Sublist (part G σ b) G.edges :=
  partFrom_sublist σ b 0 G.edges

theorem part_nodup (G : Graph) (σ : Nat → Bool) (b : Bool) (h : G.edges.Nodup) :
    (part G σ b).Nodup :=
  List.Nodup.sublist (part_sublist G σ b) h

theorem mem_edges_of_mem_part {G : Graph} {σ : Nat → Bool} {b : Bool} {e : Edge}
    (h : e ∈ part G σ b) : e ∈ G.edges :=
  (part_sublist G σ b).subset h

theorem length_partFrom (σ : Nat → Bool) (b : Bool) :
    ∀ (i0 : Nat) (es : List Edge),
      (partFrom σ b i0 es).length = cntFrom σ b i0 es.length
  | _, [] => rfl
  | i, e :: es => by
    simp only [partFrom, cntFrom]
    split
    · simp only [List.length_cons, length_partFrom σ b (i + 1) es]; omega
    · simp only [length_partFrom σ b (i + 1) es]; omega

theorem length_part (G : Graph) (σ : Nat → Bool) (b : Bool) :
    (part G σ b).length = cnt σ b G.edges.length :=
  length_partFrom σ b 0 G.edges

theorem getD_mem_partFrom (σ : Nat → Bool) (b : Bool) :
    ∀ (i0 : Nat) (es : List Edge) (j : Nat), j < es.length → σ (i0 + j) = b →
      es.getD j (0, 0) ∈ partFrom σ b i0 es
  | _, [], j, hj, _ => absurd hj (Nat.not_lt_zero j)
  | i, e :: es, 0, _, hσ => by
    simp only [Nat.add_zero] at hσ
    simp [partFrom, hσ]
  | i, e :: es, j + 1, hj, hσ => by
    have hj' : j < es.length := Nat.lt_of_succ_lt_succ hj
    have hσ' : σ (i + 1 + j) = b := by
      rw [show i + 1 + j = i + (j + 1) by omega]; exact hσ
    have ih := getD_mem_partFrom σ b (i + 1) es j hj' hσ'
    simp only [partFrom, List.getD_cons_succ]
    split
    · exact List.mem_cons_of_mem e ih
    · exact ih

theorem edgeOf_mem_part (G : Graph) (σ : Nat → Bool) {b : Bool} {j : Nat}
    (hj : j < G.edges.length) (hσ : σ j = b) : edgeOf G j ∈ part G σ b :=
  getD_mem_partFrom σ b 0 G.edges j hj (by simpa using hσ)

theorem partFrom_not (σ : Nat → Bool) (b : Bool) :
    ∀ (i0 : Nat) (es : List Edge),
      partFrom (fun i => !σ i) b i0 es = partFrom σ (!b) i0 es
  | _, [] => rfl
  | i, e :: es => by
    simp only [partFrom, partFrom_not σ b (i + 1) es]
    cases hs : σ i <;> cases b <;> simp

theorem part_not (G : Graph) (σ : Nat → Bool) (b : Bool) :
    part G (fun i => !σ i) b = part G σ (!b) :=
  partFrom_not σ b 0 G.edges

/-! ## Counting lemmas -/

theorem cntFrom_succ (σ : Nat → Bool) (b : Bool) :
    ∀ (i0 len : Nat),
      cntFrom σ b i0 (len + 1) = cntFrom σ b i0 len + (if σ (i0 + len) = b then 1 else 0)
  | i0, 0 => by simp [cntFrom]
  | i0, len + 1 => by
    rw [cntFrom, cntFrom_succ σ b (i0 + 1) len, cntFrom,
      show i0 + 1 + len = i0 + (len + 1) by omega]
    omega

theorem cnt_succ (σ : Nat → Bool) (b : Bool) (i : Nat) :
    cnt σ b (i + 1) = cnt σ b i + (if σ i = b then 1 else 0) := by
  unfold cnt
  rw [cntFrom_succ]
  simp

theorem cnt_mono (σ : Nat → Bool) (b : Bool) {i j : Nat} (h : i ≤ j) :
    cnt σ b i ≤ cnt σ b j := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp h
    subst this
    exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · have := ih (Nat.le_of_lt_succ h')
      rw [cnt_succ]
      omega
    · subst h'
      exact Nat.le_refl _

theorem cnt_succ_of_eq (σ : Nat → Bool) (b : Bool) (i : Nat) (h : σ i = b) :
    cnt σ b (i + 1) = cnt σ b i + 1 := by
  rw [cnt_succ, h]; simp

theorem cnt_succ_of_ne (σ : Nat → Bool) (b : Bool) (i : Nat) (h : ¬ σ i = b) :
    cnt σ b (i + 1) = cnt σ b i := by
  rw [cnt_succ, if_neg h, Nat.add_zero]

theorem cnt_one_le (σ : Nat → Bool) (b : Bool) : cnt σ b 1 ≤ 1 := by
  rw [cnt_succ]
  simp only [cnt, cntFrom]
  split <;> omega

/-! ## The valuation -/

theorem val_lt (G : Graph) (σ : Nat → Bool) {v : Nat} (hv : v < G.edges.length) :
    val G σ v = σ v := by
  simp [val, hv]

/-- Decoding a register index: `(i·k + j) / k = i` and `(i·k + j) % k = j`. -/
theorem reg_decode {k i j : Nat} (hk : 1 ≤ k) (hj : j < k) :
    (i * k + j) / k = i ∧ (i * k + j) % k = j := by
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]
  · exact Nat.mul_add_mod_of_lt hj

theorem reg_lt {m k i j : Nat} (hi : i < m) (hj : j < k) : i * k + j < m * k := by
  have h1 : i * k + j < (i + 1) * k := by
    rw [Nat.succ_mul]; omega
  have h2 : (i + 1) * k ≤ m * k := Nat.mul_le_mul_right k hi
  omega

theorem val_reg_true (G : Graph) (σ : Nat → Bool) {i j : Nat}
    (hk : 1 ≤ cap G) (hi : i < G.edges.length) (hj : j < cap G) :
    val G σ (reg G.edges.length (cap G) i j) =
      decide (j + 1 ≤ cnt σ true (i + 1)) := by
  have hlt := reg_lt hi hj
  obtain ⟨hdiv, hmod⟩ := reg_decode (i := i) hk hj
  have hsub : G.edges.length + i * cap G + j - G.edges.length = i * cap G + j := by omega
  simp only [val, reg]
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [hsub, hdiv, hmod]

theorem val_reg_false (G : Graph) (σ : Nat → Bool) {i j : Nat}
    (hk : 1 ≤ cap G) (hi : i < G.edges.length) (hj : j < cap G) :
    val G σ (reg (G.edges.length + G.edges.length * cap G) (cap G) i j) =
      decide (j + 1 ≤ cnt σ false (i + 1)) := by
  have hlt := reg_lt hi hj
  obtain ⟨hdiv, hmod⟩ := reg_decode (i := i) hk hj
  have hsub : G.edges.length + G.edges.length * cap G + i * cap G + j -
      (G.edges.length + G.edges.length * cap G) = i * cap G + j := by omega
  simp only [val, reg]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp only [hsub, hdiv, hmod]

/-! ## Sequential counter soundness -/

/-- Evaluation of the four clause shapes of `atMostSeq`, in terms of the
    literal values. -/
theorem eval2 (α : Nat → Bool) (a : Nat) (pa : Bool) (b : Nat) (pb : Bool) :
    CNF.Clause.eval α [(a, pa), (b, pb)] = ((α a == pa) || (α b == pb)) := by
  simp [CNF.Clause.eval]

theorem eval3 (α : Nat → Bool) (a : Nat) (pa : Bool) (b : Nat) (pb : Bool)
    (c : Nat) (pc : Bool) :
    CNF.Clause.eval α [(a, pa), (b, pb), (c, pc)] =
      ((α a == pa) || (α b == pb) || (α c == pc)) := by
  simp [CNF.Clause.eval, Bool.or_assoc]

theorem eval1 (α : Nat → Bool) (a : Nat) (pa : Bool) :
    CNF.Clause.eval α [(a, pa)] = (α a == pa) := by
  simp [CNF.Clause.eval]

/-- Sinz's counter is satisfied by the canonical register valuation whenever
    at most `k` of the literals are true. `σ` gives the literal values
    (`α i = σ i`), the registers hold the prefix counts. -/
theorem atMostSeq_sat (pol : Bool) (m k base : Nat) (α σ : Nat → Bool)
    (hm : 0 < m) (hk : 1 ≤ k)
    (hlit : ∀ i, i < m → α i = σ i)
    (hreg : ∀ i j, i < m → j < k →
      α (reg base k i j) = decide (j + 1 ≤ cnt σ pol (i + 1)))
    (hbound : cnt σ pol m ≤ k) :
    ∀ cl ∈ atMostSeq pol m k base, CNF.Clause.eval α cl = true := by
  intro cl hcl
  simp only [atMostSeq, List.mem_append, List.mem_filterMap, List.mem_range,
    List.mem_flatMap, List.mem_cons] at hcl
  rcases hcl with ⟨j, hj, hcj⟩ | ⟨i, hi, hci⟩
  · -- C0: ¬s(0, j) for 1 ≤ j < k
    split at hcj
    · exact absurd hcj (by simp)
    · next hj0 =>
      simp only [Option.some.injEq] at hcj
      subst hcj
      rw [eval1, hreg 0 j hm hj]
      have := cnt_one_le σ pol
      simp only [Nat.zero_add]
      have hlt : ¬ (j + 1 ≤ cnt σ pol 1) := by omega
      simp [hlt]
  · rcases hci with rfl | hci
    · -- C1(i): ¬lᵢ ∨ s(i, 0)
      rw [eval2, hlit i hi, hreg i 0 hi hk]
      by_cases hs : σ i = pol
      · have := cnt_succ_of_eq σ pol i hs
        have h1 : 0 + 1 ≤ cnt σ pol (i + 1) := by omega
        simp [h1]
      · have : σ i = !pol := Bool.eq_not_of_ne hs
        simp [this]
    · split at hci
      · exact absurd hci (List.not_mem_nil)
      · next hi0 =>
        simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
          List.mem_filterMap] at hci
        have him : i - 1 < m := by omega
        have hkk : k - 1 < k := by omega
        have hi1 : i - 1 + 1 = i := by omega
        rcases hci with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, hcj⟩
        · -- C4(i): ¬lᵢ ∨ ¬s(i-1, k-1)
          rw [eval2, hlit i hi, hreg (i - 1) (k - 1) him hkk, hi1]
          by_cases hs : σ i = pol
          · have h1 := cnt_succ_of_eq σ pol i hs
            have h2 := cnt_mono σ pol (i := i + 1) (j := m) hi
            have h3 : ¬ (k - 1 + 1 ≤ cnt σ pol i) := by omega
            simp [h3]
          · have : σ i = !pol := Bool.eq_not_of_ne hs
            simp [this]
        · -- C3(i, j): ¬s(i-1, j) ∨ s(i, j)
          rw [eval2, hreg (i - 1) j him hj, hreg i j hi hj, hi1]
          have h2 := cnt_mono σ pol (i := i) (j := i + 1) (Nat.le_succ i)
          by_cases h : j + 1 ≤ cnt σ pol i
          · have h' : j + 1 ≤ cnt σ pol (i + 1) := by omega
            simp [h']
          · simp [h]
        · -- C2(i, j): ¬lᵢ ∨ ¬s(i-1, j-1) ∨ s(i, j), 1 ≤ j < k
          split at hcj
          · exact absurd hcj (by simp)
          · next hj0 =>
            simp only [Option.some.injEq] at hcj
            subst hcj
            have hjk : j - 1 < k := by omega
            rw [eval3, hlit i hi, hreg (i - 1) (j - 1) him hjk, hreg i j hi hj, hi1]
            by_cases hs : σ i = pol
            · have h1 := cnt_succ_of_eq σ pol i hs
              by_cases h : j - 1 + 1 ≤ cnt σ pol i
              · have h' : j + 1 ≤ cnt σ pol (i + 1) := by omega
                simp [h']
              · simp [h]
            · have : σ i = !pol := Bool.eq_not_of_ne hs
              simp [this]

/-! ## Witness clause soundness -/

theorem chainOK_mono {E E' : List Edge} (hsub : ∀ e, e ∈ E → e ∈ E') :
    ∀ p : List Nat, chainOK E p = true → chainOK E' p = true
  | [], _ => rfl
  | [_], _ => rfl
  | u :: v :: rest, h => by
    simp only [chainOK, Bool.and_eq_true] at h ⊢
    exact ⟨List.contains_iff_mem.mpr (hsub _ (List.contains_iff_mem.mp h.1)),
      chainOK_mono hsub (v :: rest) h.2⟩

theorem pathOK_mono {E E' : List Edge} (hsub : ∀ e, e ∈ E → e ∈ E')
    (branch : List Nat) (s t : Nat) (p : List Nat) (h : pathOK E branch s t p = true) :
    pathOK E' branch s t p = true := by
  simp only [pathOK, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, h.1.1.1.2⟩, h.1.1.2⟩,
    chainOK_mono hsub p h.1.2⟩, h.2⟩

theorem valid_mono {E E' : List Edge} (hsub : ∀ e, e ∈ E → e ∈ E')
    (c : KurCert) (h : c.valid E = true) : c.valid E' = true := by
  simp only [KurCert.valid, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨⟨⟨h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩, ?_⟩, h.2⟩
  intro x hx
  exact pathOK_mono hsub c.branch x.1.1 x.1.2 x.2 (h.1.2 x hx)

theorem witness_clause_sat (G : Graph) (σ α : Nat → Bool) (w : Witness)
    (hw : w.ok G = true)
    (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (hpl : planar (part G σ w.pol))
    (hlit : ∀ i, i < G.edges.length → α i = σ i) :
    CNF.Clause.eval α w.clause = true := by
  simp only [Witness.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hidx, hvalid⟩ := hw
  cases h : CNF.Clause.eval α w.clause with
  | true => rfl
  | false =>
    exfalso
    -- every literal is false: α i = w.pol for all i ∈ w.idx
    have hall : ∀ i ∈ w.idx, σ i = w.pol := by
      intro i hi
      simp only [Witness.clause, CNF.Clause.eval, List.any_map, List.any_eq_false,
        Function.comp] at h
      have := h i hi
      rw [hlit i (hidx i hi)] at this
      cases hs : σ i <;> cases hp : w.pol <;> simp_all
    have hsub : ∀ e, e ∈ w.idx.map (edgeOf G) → e ∈ part G σ w.pol := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      exact edgeOf_mem_part G σ (hidx i hi) (hall i hi)
    exact H2 _ _ (valid_mono hsub w.cert hvalid) hpl

/-! ## Main theorems -/

/-- Unpacking `graphOK`. -/
theorem graphOK_spec {G : Graph} (h : graphOK G = true) :
    3 ≤ G.n ∧ (∀ e ∈ G.edges, e.1 < e.2 ∧ e.2 < G.n) ∧ G.edges.Nodup ∧
      0 < G.edges.length := by
  simp only [graphOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The Lift lemma: a normalised biplanar partition satisfies the formula. -/
theorem eval_mkCNF (G : Graph) (ws : List Witness)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (planar : List Edge → Prop)
    (H1 : ∀ S : List Edge, S.Nodup → (∀ e ∈ S, e.1 < e.2 ∧ e.2 < G.n) →
      planar S → S.length ≤ 3 * G.n - 6)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (σ : Nat → Bool) (hσ0 : σ 0 = false)
    (hp1 : planar (part G σ false)) (hp2 : planar (part G σ true)) :
    (mkCNF G ws).eval (val G σ) = true := by
  obtain ⟨h3n, hedges, hnodup, hpos⟩ := graphOK_spec hG
  rw [List.all_eq_true] at hws
  have hk : 1 ≤ cap G := by simp only [cap]; omega
  have hbound : ∀ b, planar (part G σ b) → cnt σ b G.edges.length ≤ cap G := by
    intro b hp
    have := H1 (part G σ b) (part_nodup G σ b hnodup)
      (fun e he => hedges e (mem_edges_of_mem_part he)) hp
    rw [length_part] at this
    exact this
  have hlit : ∀ i, i < G.edges.length → val G σ i = σ i := fun i hi => val_lt G σ hi
  rw [CNF.eval, Array.all_eq_true']
  intro cl hcl
  simp only [mkCNF, List.mem_toArray, List.mem_append, baseClauses, List.mem_cons,
    List.mem_map] at hcl
  rcases hcl with (rfl | hcl | hcl) | ⟨w, hw, rfl⟩
  · rw [eval1, hlit 0 hpos, hσ0]; rfl
  · exact atMostSeq_sat true G.edges.length (cap G) G.edges.length (val G σ) σ hpos hk
      hlit (fun i j hi hj => val_reg_true G σ hk hi hj) (hbound true hp2) cl hcl
  · exact atMostSeq_sat false G.edges.length (cap G)
      (G.edges.length + G.edges.length * cap G) (val G σ) σ hpos hk hlit
      (fun i j hi hj => val_reg_false G σ hk hi hj) (hbound false hp1) cl hcl
  · exact witness_clause_sat G σ (val G σ) w (hws w hw) planar H2
      (by cases hp : w.pol <;> simp [hp1, hp2]) hlit

/-- Counter-free Lift: the unit and the witness clauses need only (H2). -/
theorem eval_mkCNF₀ (G : Graph) (ws : List Witness)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S)
    (σ : Nat → Bool) (hσ0 : σ 0 = false)
    (hp1 : planar (part G σ false)) (hp2 : planar (part G σ true)) :
    (mkCNF₀ G ws).eval (val G σ) = true := by
  obtain ⟨_, _, _, hpos⟩ := graphOK_spec hG
  rw [List.all_eq_true] at hws
  have hlit : ∀ i, i < G.edges.length → val G σ i = σ i := fun i hi => val_lt G σ hi
  rw [CNF.eval, Array.all_eq_true']
  intro cl hcl
  simp only [mkCNF₀, List.mem_toArray, List.mem_cons, List.mem_map] at hcl
  rcases hcl with rfl | ⟨w, hw, rfl⟩
  · rw [eval1, hlit 0 hpos, hσ0]; rfl
  · exact witness_clause_sat G σ (val G σ) w (hws w hw) planar H2
      (by cases hp : w.pol <;> simp [hp1, hp2]) hlit

/-- **Counter-free conditional non-biplanarity**: hypothesis (H2) only. -/
theorem not_biplanar_of_unsat₀ (G : Graph) (ws : List Witness)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hunsat : (mkCNF₀ G ws).Unsat)
    (planar : List Edge → Prop)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S) :
    ¬ Biplanar planar G := by
  intro ⟨σ, h1, h2⟩
  have key : ∀ σ : Nat → Bool, σ 0 = false → planar (part G σ false) →
      planar (part G σ true) → False := by
    intro σ hσ0 hp1 hp2
    have := hunsat (val G σ)
    rw [eval_mkCNF₀ G ws hG hws planar H2 σ hσ0 hp1 hp2] at this
    exact Bool.noConfusion this
  cases hσ0 : σ 0 with
  | false => exact key σ hσ0 h1 h2
  | true =>
    refine key (fun i => !σ i) (by simp [hσ0]) ?_ ?_
    · rw [part_not]; exact h2
    · rw [part_not]; exact h1

/-- **Conditional non-biplanarity from an UNSAT certificate.** -/
theorem not_biplanar_of_unsat (G : Graph) (ws : List Witness)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hunsat : (mkCNF G ws).Unsat)
    (planar : List Edge → Prop)
    (H1 : ∀ S : List Edge, S.Nodup → (∀ e ∈ S, e.1 < e.2 ∧ e.2 < G.n) →
      planar S → S.length ≤ 3 * G.n - 6)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S) :
    ¬ Biplanar planar G := by
  intro ⟨σ, h1, h2⟩
  have key : ∀ σ : Nat → Bool, σ 0 = false → planar (part G σ false) →
      planar (part G σ true) → False := by
    intro σ hσ0 hp1 hp2
    have := hunsat (val G σ)
    rw [eval_mkCNF G ws hG hws planar H1 H2 σ hσ0 hp1 hp2] at this
    exact Bool.noConfusion this
  cases hσ0 : σ 0 with
  | false => exact key σ hσ0 h1 h2
  | true =>
    refine key (fun i => !σ i) (by simp [hσ0]) ?_ ?_
    · rw [part_not]; exact h2
    · rw [part_not]; exact h1

/-- **Cube-leaf variant.** A refuted leaf `cube ∪ F` leaves no normalised
    biplanar partition inside the cube. -/
theorem not_biplanar_on_cube_of_unsat (G : Graph) (ws : List Witness)
    (cube : LRATCatcher.Cube)
    (hG : graphOK G = true) (hws : ws.all (Witness.ok G) = true)
    (hunsat : (LRATCatcher.Cube.leafCNF cube (mkCNF G ws)).Unsat)
    (planar : List Edge → Prop)
    (H1 : ∀ S : List Edge, S.Nodup → (∀ e ∈ S, e.1 < e.2 ∧ e.2 < G.n) →
      planar S → S.length ≤ 3 * G.n - 6)
    (H2 : ∀ (S : List Edge) (c : KurCert), c.valid S = true → ¬ planar S) :
    ¬ ∃ σ : Nat → Bool, σ 0 = false ∧ cube.sat (val G σ) = true ∧
        planar (part G σ false) ∧ planar (part G σ true) := by
  intro ⟨σ, hσ0, hcube, hp1, hp2⟩
  have := hunsat (val G σ)
  simp only [LRATCatcher.Cube.leafCNF, CNF.eval_append, LRATCatcher.Cube.eval_toCNF,
    hcube, eval_mkCNF G ws hG hws planar H1 H2 σ hσ0 hp1 hp2, Bool.and_self] at this
  exact Bool.noConfusion this

end Biplanar
