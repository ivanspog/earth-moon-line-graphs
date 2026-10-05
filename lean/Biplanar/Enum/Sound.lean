import Biplanar.Enum.Defs
import Biplanar.Lift
import Biplanar.Sym

/-!
# Biplanar.Enum.Sound — what a checked certificate proves

* `euler_sound`: an Euler witness (a vertex list `W` with more than `6|W| − 12` edges inside)
  refutes biplanarity under (H4);
* `tf_sound`: a triangle-free witness (more than `4|W| − 8` triangle-free edges inside `W`)
  refutes biplanarity under (H5);
* `iso_sound`: a checked isomorphism transports biplanarity to the target graph under (H3).
-/

namespace Biplanar.Enum
open Biplanar

/-! ## The checkers -/

/-- `W` is an Euler witness for `G`. -/
def eulerWitOK (G : Graph) (W : List Nat) : Bool :=
  graphOK G && decide W.Nodup && decide (3 ≤ W.length) &&
    decide (6 * W.length - 12 < (G.edges.filter (inside W)).length)

/-- Boolean triangle test for sorted edge lists: no `(x, y), (x, z)` with `y < z` and `(y, z)`. -/
def triFreeB (T : List Edge) : Bool :=
  T.all (fun e => T.all (fun f => !(e.1 == f.1 && decide (e.2 < f.2) && T.contains (e.2, f.2))))

/-- `(W, T)` is a triangle-free witness for `G`. -/
def tfWitOK (G : Graph) (W : List Nat) (T : List Edge) : Bool :=
  graphOK G && decide W.Nodup && decide (3 ≤ W.length) && decide T.Nodup &&
    T.all (fun e => G.edges.contains e && inside W e) && triFreeB T &&
    decide (4 * W.length - 8 < T.length)

/-- Lexicographic order on edges (only used to compare edge sets by sorting). -/
def edgeLE (e f : Edge) : Bool := decide (e.1 < f.1) || (e.1 == f.1 && decide (e.2 ≤ f.2))

/-- `π` maps the edge set of `Gs` onto the edge set of `Gt`. -/
def isoOK (Gs Gt : Graph) (π : List Nat) : Bool :=
  (Gs.n == Gt.n) && permOK Gs.n π && graphOK Gs && graphOK Gt &&
    ((Gs.edges.map (applyPerm π)).mergeSort edgeLE == Gt.edges.mergeSort edgeLE)

/-! ## Facts about `graphOK` and partitions -/

theorem graphOK_spec {G : Graph} (h : graphOK G = true) :
    3 ≤ G.n ∧ (∀ e ∈ G.edges, e.1 < e.2 ∧ e.2 < G.n) ∧ G.edges.Nodup := by
  simp only [graphOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := h
  exact ⟨h1, fun e he => by simpa using h2 e he, h3⟩

theorem filter_length_partFrom (σ : Nat → Bool) (p : Edge → Bool) :
    ∀ (i : Nat) (es : List Edge), (es.filter p).length =
      ((partFrom σ false i es).filter p).length + ((partFrom σ true i es).filter p).length
  | _, [] => by simp [partFrom]
  | i, e :: es => by
    have ih := filter_length_partFrom σ p (i + 1) es
    cases h : σ i <;> cases hp : p e <;> simp [partFrom, h, hp, List.filter_cons] <;> omega

theorem mem_partFrom_or (σ : Nat → Bool) :
    ∀ (i : Nat) (es : List Edge) (e : Edge), e ∈ es →
      e ∈ partFrom σ false i es ∨ e ∈ partFrom σ true i es
  | _, [], _, h => by simp at h
  | i, a :: es, e, h => by
    have ih := mem_partFrom_or σ (i + 1) es e
    rcases List.mem_cons.mp h with rfl | h
    · cases hs : σ i <;> simp [partFrom, hs]
    · rcases ih h with h' | h' <;> cases hs : σ i <;> simp [partFrom, hs, h']

theorem partFrom_disjoint (σ : Nat → Bool) :
    ∀ (i : Nat) (es : List Edge), es.Nodup → ∀ e,
      e ∈ partFrom σ false i es → e ∈ partFrom σ true i es → False
  | _, [], _, _, h, _ => by simp [partFrom] at h
  | i, a :: es, hnd, e, h0, h1 => by
    have hnd' := (List.nodup_cons.mp hnd)
    have ih := partFrom_disjoint σ (i + 1) es hnd'.2 e
    cases hs : σ i
    · simp only [partFrom, hs, if_true, if_false, Bool.false_eq_true, ite_true, ite_false,
        reduceCtorEq] at h0 h1
      rcases List.mem_cons.mp h0 with rfl | h0
      · exact hnd'.1 ((partFrom_sublist σ true (i + 1) es).subset h1)
      · exact ih h0 h1
    · simp only [partFrom, hs, if_true, if_false, Bool.false_eq_true, ite_true, ite_false,
        reduceCtorEq] at h0 h1
      rcases List.mem_cons.mp h1 with rfl | h1
      · exact hnd'.1 ((partFrom_sublist σ false (i + 1) es).subset h0)
      · exact ih h0 h1

theorem length_le_filter_add {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true ∨ q x = true) →
      l.length ≤ (l.filter p).length + (l.filter q).length
  | [], _ => by simp
  | x :: l, h => by
    have ih := length_le_filter_add p q l (fun y hy => h y (List.mem_cons_of_mem x hy))
    rcases h x (List.mem_cons_self) with hx | hx <;>
      cases hp : p x <;> cases hq : q x <;> simp_all [List.filter_cons] <;> omega

/-! ## Euler witnesses -/

theorem euler_sound {planar : List Edge → Prop} (HE : EulerHyp planar) {G : Graph}
    {W : List Nat} (h : eulerWitOK G W = true) : ¬ Biplanar planar G := by
  rintro ⟨σ, h0, h1⟩
  simp only [eulerWitOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hG, hW⟩, h3⟩, hc⟩ := h
  obtain ⟨_, hwf, hnd⟩ := graphOK_spec hG
  have wf : ∀ b, ∀ e ∈ part G σ b, e.1 < e.2 := fun b e he =>
    (hwf e (mem_edges_of_mem_part he)).1
  have b0 := HE _ h0 (part_nodup G σ false hnd) (wf false) W hW h3
  have b1 := HE _ h1 (part_nodup G σ true hnd) (wf true) W hW h3
  have hs := filter_length_partFrom σ (inside W) 0 G.edges
  simp only [part] at b0 b1
  omega

/-! ## Triangle-free witnesses -/

theorem triFreeB_sound {T : List Edge} (hwf : ∀ e ∈ T, e.1 < e.2) (h : triFreeB T = true) :
    TriFree T := by
  intro x y z hxy hxz hyz
  simp only [triFreeB, List.all_eq_true] at h
  have := h _ hxy _ hxz
  have hlt := hwf _ hyz
  simp only at hlt
  simp [hlt, List.contains_iff_mem, hyz] at this

theorem triFree_sub {T T' : List Edge} (hs : ∀ e ∈ T', e ∈ T) (h : TriFree T) : TriFree T' :=
  fun x y z h1 h2 h3 => h x y z (hs _ h1) (hs _ h2) (hs _ h3)

theorem tf_sound {planar : List Edge → Prop} (HT : TriFreeHyp planar) {G : Graph}
    {W : List Nat} {T : List Edge} (h : tfWitOK G W T = true) : ¬ Biplanar planar G := by
  rintro ⟨σ, h0, h1⟩
  simp only [tfWitOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hG, hW⟩, h3⟩, hTnd⟩, hTin⟩, htf⟩, hc⟩ := h
  obtain ⟨_, hwf, hnd⟩ := graphOK_spec hG
  have hTG : ∀ e ∈ T, e ∈ G.edges ∧ inside W e = true := fun e he => by
    have := hTin e he
    simp only [Bool.and_eq_true, List.contains_iff_mem] at this
    exact this
  have tfT : TriFree T := triFreeB_sound (fun e he => (hwf e (hTG e he).1).1) htf
  have wf : ∀ b, ∀ e ∈ part G σ b, e.1 < e.2 := fun b e he =>
    (hwf e (mem_edges_of_mem_part he)).1
  have bound : ∀ b, planar (part G σ b) →
      (T.filter (fun e => (part G σ b).contains e)).length ≤ 2 * W.length - 4 := by
    intro b hp
    refine HT _ hp (part_nodup G σ b hnd) (wf b) W hW h3 _
      (List.Pairwise.filter _ hTnd) ?_ ?_
    · intro e he
      rw [List.mem_filter] at he
      exact ⟨by simpa [List.contains_iff_mem] using he.2, (hTG e he.1).2⟩
    · exact triFree_sub (fun e he => (List.mem_filter.mp he).1) tfT
  have cover := length_le_filter_add (fun e => (part G σ false).contains e)
    (fun e => (part G σ true).contains e) T (fun e he => by
      rcases mem_partFrom_or σ 0 G.edges e (hTG e he).1 with h' | h'
      · left; simpa [part, List.contains_iff_mem] using h'
      · right; simpa [part, List.contains_iff_mem] using h')
  have := bound false h0
  have := bound true h1
  omega

/-! ## Isomorphisms -/

theorem permOK_spec {n : Nat} {π : List Nat} (h : permOK n π = true) :
    π.length = n ∧ (∀ v ∈ π, v < n) ∧ π.Nodup := by
  simp only [permOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem perm_getD_inj {n : Nat} {π : List Nat} (h : permOK n π = true) {u v : Nat}
    (hu : u < n) (hv : v < n) (huv : π.getD u u = π.getD v v) : u = v := by
  obtain ⟨hl, _, hnd⟩ := permOK_spec h
  have hu' : u < π.length := hl ▸ hu
  have hv' : v < π.length := hl ▸ hv
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu',
    List.getElem?_eq_getElem hv'] at huv
  exact (List.getElem_inj hnd).mp (by simpa using huv)

theorem applyPerm_inj {n : Nat} {π : List Nat} (h : permOK n π = true) {e f : Edge}
    (he : e.1 < e.2 ∧ e.2 < n) (hf : f.1 < f.2 ∧ f.2 < n)
    (hef : applyPerm π e = applyPerm π f) : e = f := by
  obtain ⟨e1, e2⟩ := e
  obtain ⟨f1, f2⟩ := f
  simp only at he hf
  have i11 := fun hh => perm_getD_inj h (by omega : e1 < n) (by omega : f1 < n) hh
  have i22 := fun hh => perm_getD_inj h (by omega : e2 < n) (by omega : f2 < n) hh
  have i12 := fun hh => perm_getD_inj h (by omega : e1 < n) (by omega : f2 < n) hh
  have i21 := fun hh => perm_getD_inj h (by omega : e2 < n) (by omega : f1 < n) hh
  simp only [applyPerm, normEdge] at hef
  split at hef <;> split at hef <;> simp only [Prod.mk.injEq] at hef <;>
    obtain ⟨ha, hb⟩ := hef
  · rw [i11 ha, i22 hb]
  · have := i12 ha; have := i21 hb; omega
  · have := i21 ha; have := i12 hb; omega
  · rw [i11 hb, i22 ha]

theorem partFrom_eq_filter (g : Edge → Bool) (b : Bool) (σ : Nat → Bool) :
    ∀ (i : Nat) (es : List Edge), (∀ j (hj : j < es.length), σ (i + j) = g es[j]) →
      partFrom σ b i es = es.filter (fun e => g e == b)
  | _, [], _ => by simp [partFrom]
  | i, e :: es, h => by
    have h0 : σ i = g e := by simpa using h 0 (by simp)
    have ih := partFrom_eq_filter g b σ (i + 1) es (fun j hj => by
      have := h (j + 1) (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega] at this
      simpa using this)
    rw [show partFrom σ b i (e :: es) = if σ i = b then e :: partFrom σ b (i + 1) es
      else partFrom σ b (i + 1) es from rfl, h0, ih, List.filter_cons]
    cases b <;> cases g e <;> simp

theorem iso_sound {planar : List Edge → Prop} {Gs Gt : Graph} {π : List Nat}
    (H3 : IsoInvariant Gt planar) (h : isoOK Gs Gt π = true) :
    Biplanar planar Gs → Biplanar planar Gt := by
  rintro ⟨σ, h0, h1⟩
  simp only [isoOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hn, hπ⟩, hGs⟩, hGt⟩, hsort⟩ := h
  obtain ⟨_, wfs, nds⟩ := graphOK_spec hGs
  obtain ⟨_, wft, ndt⟩ := graphOK_spec hGt
  -- the image of the edge set of `Gs` is the edge set of `Gt`
  have hperm : (Gs.edges.map (applyPerm π)).Perm Gt.edges := by
    have p1 := (List.mergeSort_perm (Gs.edges.map (applyPerm π)) edgeLE).symm
    rw [hsort] at p1
    exact p1.trans (List.mergeSort_perm _ _)
  have img : ∀ f, f ∈ Gt.edges ↔ f ∈ Gs.edges.map (applyPerm π) := fun f =>
    (hperm.mem_iff).symm
  let S1 := (part Gs σ true).map (applyPerm π)
  let g : Edge → Bool := fun e => S1.contains e
  let σ' : Nat → Bool := fun j => g (edgeOf Gt j)
  have hpart : ∀ b, part Gt σ' b = Gt.edges.filter (fun e => g e == b) := fun b =>
    partFrom_eq_filter g b σ' 0 Gt.edges (fun j hj => by
      simp [σ', edgeOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj])
  have hπ' : permOK Gt.n π = true := hn ▸ hπ
  have wfs' : ∀ b, ∀ e ∈ part Gs σ b, e.1 < e.2 ∧ e.2 < Gt.n := fun b e he =>
    hn ▸ wfs e (mem_edges_of_mem_part he)
  have wft' : ∀ b, ∀ e ∈ part Gt σ' b, e.1 < e.2 ∧ e.2 < Gt.n := fun b e he =>
    wft e (mem_edges_of_mem_part he)
  -- membership in the new parts
  have mem1 : ∀ f, f ∈ part Gt σ' true ↔ f ∈ S1 := by
    intro f
    rw [hpart true, List.mem_filter]
    constructor
    · rintro ⟨_, hf⟩; simpa [g, List.contains_iff_mem] using hf
    · intro hf
      refine ⟨?_, by simpa [g, List.contains_iff_mem] using hf⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hf
      exact (img _).mpr (List.mem_map_of_mem (mem_edges_of_mem_part he))
  have mem0 : ∀ f, f ∈ part Gt σ' false ↔ f ∈ (part Gs σ false).map (applyPerm π) := by
    intro f
    rw [hpart false, List.mem_filter]
    constructor
    · rintro ⟨hf, hg⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ((img f).mp hf)
      rcases mem_partFrom_or σ 0 Gs.edges e he with h' | h'
      · exact List.mem_map_of_mem h'
      · exfalso
        have : g (applyPerm π e) = true := by
          simp only [g, S1, List.contains_iff_mem]
          exact List.mem_map_of_mem h'
        simp [this] at hg
    · intro hf
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hf
      refine ⟨(img _).mpr (List.mem_map_of_mem (mem_edges_of_mem_part he)), ?_⟩
      cases hgv : g (applyPerm π e)
      · rfl
      · exfalso
        simp only [g, S1, List.contains_iff_mem] at hgv
        obtain ⟨e', he', hee'⟩ := List.mem_map.mp hgv
        have := applyPerm_inj hπ' (wfs' false e he) (wfs' true e' he') hee'.symm
        exact partFrom_disjoint σ 0 Gs.edges nds e he (this ▸ he')
  refine ⟨σ', ?_, ?_⟩
  · exact (H3 π _ _ hπ' (part_nodup Gs σ false nds) (part_nodup Gt σ' false ndt)
      (wfs' false) (wft' false) mem0).mp h0
  · exact (H3 π _ _ hπ' (part_nodup Gs σ true nds) (part_nodup Gt σ' true ndt)
      (wfs' true) (wft' true) mem1).mp h1

end Biplanar.Enum
