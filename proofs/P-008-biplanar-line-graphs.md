# P-008 — Every biplanar line graph is 9-colourable; fractional bounds for line graphs and for joins with a large clique

**Status:** proven. The 22 finite cases of fact (L5) are machine-checked in Lean 4 (`lean/`). The rest
is a written proof that relies on two machine enumerations, (F32) and (F5). Those enumerations are
Python code, each re-derived independently, but not machine-checked. **Not peer-reviewed.** The proof
went through three rounds of adversarial review by AI models from three different model families.
Every round found no gap in any bound. The last round was blind: the reviewer saw only the
mathematics, not the earlier verdicts. This is cross-model review, not peer review (see the README).

**Main result (Corollary A(iv)).** Every biplanar line graph L(H) of a loopless multigraph H has
χ_f(L(H)) ≤ 9 and χ(L(H)) ≤ 9. So no line graph of a multigraph is a 10-chromatic biplanar graph.

## Setting and facts used

φ₂ := sup{χ_f(G) : G biplanar}. Facts quoted, not re-proved:

* **(E)** Euler: every subgraph of a biplanar graph on m ≥ 3 vertices has ≤ 6m − 12 edges.
  Also, K₉ is not biplanar, so ω ≤ 8.
* **(M)** Edmonds' matching-polytope theorem (J. Edmonds, J. Res. NBS 69B (1965) 125–130),
  applied to multigraphs. Parallel edges are separate coordinates.
* **(Sz)** Szeider, arXiv:2609.28102: a biplanar graph with α ≤ 2 is 9-colourable.
  Used only in a remark; no proof step depends on it.
* **(T)** Triangle-free count: a triangle-free subgraph of a biplanar graph on n ≥ 3 vertices has
  ≤ 4n − 8 edges (by Euler's formula a triangle-free planar graph on n ≥ 3 vertices has ≤ 2n − 4
  edges, since every face has length ≥ 4).
* **(P3)** A biplanar graph with α ≤ 2 has at most 19 vertices (P-003 of the earlier deposit,
  doi:10.5281/zenodo.22242268; Szeider, arXiv:2609.28102, proves more: at most 18).
* **(R)** Reed's fractional theorem, χ_f ≤ (Δ + 1 + ω)/2 (Molloy–Reed; Edwards–King 2012, Thm 1).
* **(F32)** The machine enumeration (`verifier/f032_enumerate.py` → `f032_analyse.py` →
  `f033_line_graph_route.py` → `f034_hereditary_trifree.py`):
  * the 7-vertex loopless multigraphs with every degree 8 and every triple multiplicity sum ≤ 8,
    after the necessary biplanarity conditions (global and per-component Euler, hereditary
    Euler, containment of a 19-vertex line graph of a 5-vertex root, all of which are
    non-biplanar by (F5), the triangle-free count 4n − 8, and the
    hereditary triangle-free MaxSAT), leave exactly **22** multigraphs M;
  * these are the **A4 list** of 22 graphs (`verifier/f034_a4_line_graph_sat.py --list`). Every L(M)
    there has
    χ_f = 28/3 (`verifier/f037_lemma_tests.py`).
  * The enumeration caps multiplicities only through the degree and triple-sum constraints, so
    multiplicities up to 8 are included.
  * It has been re-derived independently twice, with separately written code. One re-derivation
    used no Euler prune in the enumeration: 10,218 classes → 73 → 56 → 30 → 22, every kill backed
    by a verified witness, and a match with the A4 list up to isomorphism.
* **(F5)** The |S| = 5 enumeration (`verifier/f037_k2check.py`). The loopless 5-vertex multigraphs with Δ ≤ 8, triple sums ≤ 8
  and e ∈ {19, 20} number 139 + 18 isomorphism classes. **Every one of them has a line graph
  violating Euler or (T)**, each kill with a verified witness. It was re-derived
  a second time with structurally different code (support × Aut enumeration and a
  CaDiCaL cardinality SAT), and got the same 139 + 18, all killed. The 20-edge ones also
  die by (P3), since n = 20 > 19.
* **(GS)** Goldberg–Seymour (proved by Chen, Jing and Zang): every loopless
  multigraph H has χ′(H) ≤ max{Δ(H) + 1, ⌈Γ(H)⌉}, with Γ as in Lemma A1. Used only for the integer
  form of A(iv).
* **(L5)** The 22 graphs of (F32) are not biplanar (the Lean 4 package in `lean/`; see the README). For each member
  i = 00, …, 21 there is a Lean 4 (v4.30) theorem, built with 0 errors, of the form

      theorem not_biplanar (planar : List Biplanar.Edge → Prop)
          (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S)
          (H3 : Biplanar.IsoInvariant G planar) :
          ¬ Biplanar.Biplanar planar G

  Here:
  * G is an explicit 28-vertex edge list.
  * `Biplanar planar G := ∃ σ : ℕ → Bool, planar (part G σ false) ∧ planar (part G σ true)`.
    That is, some 2-colouring of the edge list has both colour classes `planar`.
  * `c.valid S` checks that c exhibits a subdivision of K₅ or K₃,₃ inside the edge set S: distinct
    branch vertices, one path per branch pair, and pairwise internally disjoint paths.
  * `IsoInvariant G planar` says that `planar` is invariant under relabelling the n vertices.

  Ordinary planarity of the graph ({0, …, n−1}, S) satisfies (H2), by the elementary direction of
  Kuratowski's theorem (subdivisions of K₅ and K₃,₃ are non-planar, and planarity is closed
  under subgraphs). It also satisfies (H3). So each theorem gives "G is not biplanar".

  The proofs are by Lean-checked LRAT refutation of a CNF built from Kuratowski witness clauses,
  plus lexicographic symmetry-breaking clauses whose soundness is proved in Lean from (H3). Large
  members are split into cubes; a separately checked cover certificate shows that the cubes
  exhaust all assignments.

  Trusted: the Lean kernel, the compiler (`native_decide`) and the LRAT checker library.

  An independent audit (`verifier/f038_a4_audit.py`) checks four things for every member:
  * the theorem statement is verbatim the one above;
  * the axioms used are only propext, Classical.choice, Quot.sound and `native_decide`
    auxiliaries;
  * G is isomorphic to L(M_i), computed by networkx and not by the solver's code;
  * M_i equals the i-th member of the recomputed (F32) list and the multigraph of the original run.

  Result: 22/22, 0 failing.

## Theorem A (line graphs)

Let H be a loopless multigraph with L(H) biplanar. Write μ(H) for the maximum edge multiplicity.

* **(i)** If μ(H) ≤ 3 then χ_f(L(H)) ≤ 9. If μ(H) ≤ 2 then χ_f(L(H)) ≤ 8, and K₈ = L(K₁,₈) shows
  this is sharp. K₈ is biplanar: it is the subgraph of K₅ ∨ C₈² on the five apexes and a rim
  triangle (Appendix).
* **(ii)** χ_f(L(H)) > 9 **iff** there is a set S of 7 vertices of H such that M = H[S] has
  e(M) = 28 and L(M) is isomorphic to one of the 22 A4 graphs. Every vertex of S then has degree 8
  in M, so no edge of H joins S to V(H) ∖ S, and L(M) is a union of components of L(H). In that
  case χ_f(L(H)) ≥ 28/3.
* **(iii) Unconditionally, χ_f(L(H)) ≤ 28/3.** More precisely, **χ_f(L(H)) ∈ [0, 9] ∪ {28/3}**, and
  χ_f(L(H)) > 9 ⟺ some 7 vertices of H span 28 edges. This uses (F5), but not (F32).
* Hence **φ₂ restricted to line graphs of multigraphs is ≤ 28/3, and it is ≤ 9 iff none of the 22
  A4 graphs is biplanar.**
* **(iv) Corollary.** By (L5), none of the 22 A4 graphs is biplanar. So **every biplanar
  line graph L(H) of a loopless multigraph has χ_f(L(H)) ≤ 9**, and, by (GS),
  **χ(L(H)) ≤ 9**. In particular, no line graph of a multigraph is a 10-chromatic biplanar
  graph.

**Lemma A1 (Edmonds; fractional chromatic index).** For H with at least one edge,
χ_f(L(H)) = max{ Δ(H), Γ(H) }, where Γ(H) := max over odd S ⊆ V(H) with |S| ≥ 3 of
2e_H(S)/(|S| − 1), and **Γ(H) := 0 if H has fewer than 3 vertices** (no such S).

This is the multigraph fractional chromatic index formula: Seymour 1979 (Proc. LMS 38); Stahl
1979; Scheinerman–Ullman, *Fractional Graph Theory*, §4.2.

*Proof.*

* **(≥)** Independent sets of L(H) are matchings of H. A matching covers at most 1 edge at a
  vertex, and at most (|S| − 1)/2 edges inside an odd set S. So a fractional colouring of weight t
  has t ≥ d(v) and t ≥ 2e(S)/(|S| − 1).
* **(≤)** Set t = max(Δ, Γ) and x_e = 1/t. Then x ≥ 0, x(δ(v)) ≤ 1, and
  x(E(S)) ≤ (|S| − 1)/2 for every odd S. By (M), x is a convex combination Σ λ_M 1_M of matchings.
  The weights tλ_M give a fractional colouring of weight t. ∎

**Machine check:** `f037_theoremA_checks.py` (A-L1) compares the formula with the exact LP on 271
random multigraph roots (≤ 6 vertices, multiplicities ≤ 4). They agree in all cases.

**Lemma A2 (Euler for bounded-multiplicity roots).** Let S ⊆ V(H), s = |S|,
m = e_H(S) ≥ 3, and suppose μ(H[S]) ≤ r. Then

  **2m²/s − (r + 13)m/2 + 12 ≤ 0.**

Also Δ(H) ≤ 8, and every 3-vertex sub-multigraph has ≤ 8 edges.

*Proof.*

1. J = H[S] gives an induced subgraph L(J) of L(H), so L(J) is biplanar with m vertices, and
   e(L(J)) ≤ 6m − 12.
2. Count incident pairs: e(L(J)) = Σ_v C(d_J(v), 2) − Σ_uv C(a_uv, 2). A parallel pair is counted
   at both of its endpoints, so it is subtracted once.
3. Cauchy–Schwarz gives Σ_v C(d_J(v), 2) ≥ 2m²/s − m.
4. Since a_uv ≤ r, C(a_uv, 2) ≤ (r − 1)a_uv/2, and Σ a_uv = m.
5. Hence e(L(J)) ≥ 2m²/s − (r + 1)m/2. Compare with step 1.
6. The edges at a vertex, and the edges inside a 3-set, are pairwise intersecting. So they form
   cliques of L(H), and there are ≤ 8 of each. ∎

**Machine check:** the identity in step 2 was checked on the same 271 roots (A-L2).

**Lemma A3 (five root vertices).** If L(H) is biplanar, then every 5 vertices of H span at most 18
edges.

*Proof.*

1. Let |S| = 5. Then e(S) ≤ 5·8/2 = 20, because Δ(H) ≤ 8.
2. M′ = H[S] is loopless with Δ ≤ 8 and triple sums ≤ 8 (A2).
3. L(M′) is an induced subgraph of L(H), hence biplanar. So it satisfies Euler and (T).
4. **By (F5)**, no such M′ has 19 or 20 edges. ∎

*Remark.* L(M′) has α ≤ 2, because a matching in a 5-vertex multigraph has ≤ 2 edges. So Szeider's
(Sz), or (P3) when e = 20, gives the same conclusion by a different route. The proof does not
use them.

*Proof of (i).* By A1 and A2 we need Γ ≤ 9 (resp. ≤ 8).

* **|S| = 3:** e(S) ≤ 8, so 2e/(|S| − 1) ≤ 8.
* **Odd s ≥ 5, μ ≤ 3:**
  1. Suppose 2m/(s − 1) > 9. Then m ≥ m₀ := (9s − 7)/2.
  2. Set F(m) := 2m²/s − 8m + 12. Then F′(m) ≥ 10 − 14/s > 0 on m ≥ m₀.
  3. F(m₀) = 9s/2 − 23 + 49/(2s). This is 22/5 at s = 5 and increasing in s.
  4. So F(m) > 0, which contradicts A2 with r = 3.
* **μ ≤ 2 (threshold 8):**
  1. Suppose 2m/(s − 1) > 8. Then m ≥ 4s − 3.
  2. Set Q(m) := 2m²/s − (15/2)m + 12. Then Q′ ≥ 17/2 − 12/s > 0.
  3. Q(4s − 3) = 2s − 27/2 + 18/s. This is 1/10 at s = 5 and increasing.
  4. So Q > 0, a contradiction. ∎

**Machine check:** A-L3/A-L4 confirm, for every odd s < 1000 and every admissible m, that the
inequality of A2 fails. The minimum residuals are 22/5 and 1/10, both at s = 5.

*Proof of (ii).*

1. **Setup.** Let χ_f(L(H)) > 9. Since Δ(H) ≤ 8 (A2), A1 gives an odd S with e(S) > 9(|S| − 1)/2.
   Degrees give e(S) ≤ 8|S|/2 = 4|S|. So 9(|S| − 1)/2 < 4|S|, i.e. |S| < 9: |S| ∈ {3, 5, 7}.
2. **|S| = 3** is impossible, since e(S) ≤ 8 by A2.
3. **|S| = 5** would need e(S) ≥ 19, which contradicts **Lemma A3**.
4. **|S| = 7.** Then e(S) ≥ 28 ≥ 4|S|, so M := H[S] has exactly 28 edges and every vertex of S has
   degree 8 inside M. (So no edge of H leaves S from these vertices.)
   * Every triple multiplicity sum of M is ≤ 8 (A2).
   * L(M) is an induced subgraph of L(H), hence biplanar. So L(M) passes every necessary
     condition applied in (F32), and M is one of the 22.
5. **Converse.** If L(M) is one of the 22 and is an induced subgraph of L(H), then
   χ_f(L(H)) ≥ χ_f(L(M)) = 28/3. ∎

*Proof of (iii).* By A1 and Δ ≤ 8 it suffices to bound 2e(S)/(|S| − 1) for odd S:

* |S| = 3: ≤ 8.
* |S| = 5: e(S) ≤ 18 by **Lemma A3**, so the ratio is ≤ 36/4 = 9.
* |S| = 7: e(S) ≤ 28, so the ratio is ≤ 56/6 = 28/3. It exceeds 9 only if e(S) = 28: 2·27/6 = 9.
* |S| ≥ 9: 2e(S)/(|S| − 1) ≤ 8|S|/(|S| − 1) ≤ 9.

So Γ ≤ 9 unless some 7 vertices span 28 edges, and then Γ = 28/3. Since χ_f = max(Δ, Γ) and
Δ ≤ 8, χ_f ∈ [0, 9] ∪ {28/3}.

Conversely, 7 vertices spanning 28 edges give Γ ≥ 28/3. That gives the "⟺" of (iii), which uses
(F5) only. (ii) adds, via (F32), that the 7-vertex root is one of the 22. ∎


*Proof of (iv).* By (ii) and (L5), χ_f(L(H)) ≤ 9. So Γ(H) ≤ 9 by A1, and Δ(H) ≤ 8 by A2.
(GS) then gives χ(L(H)) = χ′(H) ≤ max{9, 9} = 9. ∎

*Integer corollary.* By Goldberg–Seymour (GS),
χ(L(H)) ≤ max(Δ + 1, ⌈Γ⌉). So under (i), μ ≤ 3 gives χ(L(H)) ≤ 9. The bound
Σ C(m_ij, 2) ≥ 40 against Σ m_ij = 28 for a 7-vertex root, which forces the multiplicities to
concentrate, is the s = 7 case of A2.

## Theorem B (joins with a large clique)

**If K_s ∨ H is biplanar with s ≥ 5 and H arbitrary, then χ_f(K_s ∨ H) ≤ 9.** K₅ ∨ C₈² shows
this is sharp.

It has χ_f = 9, and it is biplanar: the explicit two-layer partition is in the Appendix and in
`population/satprop_f034-K5vC8sq_partition.json`. It was verified with networkx and with the
Boyer planarity test, and re-verified independently.

*Proof.* We have χ_f(K_s ∨ H) = s + χ_f(H) and ω(H) ≤ 8 − s. For a vertex-minimal S ⊆ V(H) with
χ_f(H[S]) > 9 − s, the extension lemma L1 below gives δ(H[S]) ≥ 9 − s. K_s ∨ H[S] is a subgraph
of the join, so (E) applies to it.

* **s = 8:** H = ∅, since ω ≤ 8.
* **s ≥ 9:** no such biplanar join exists.
* **s = 7:** H is edgeless, so χ_f ≤ 8.
* **s = 6:** δ ≥ 3 and e(S) ≤ 9, so |S| ≤ 6 and H[S] is triangle-free. But every triangle-free
  graph on ≤ 6 vertices has χ_f ≤ 5/2.
* **s = 5:** δ ≥ 4 and e(S) ≤ |S| + 8, so |S| ≤ 8.
  * |S| = 8 forces H[S] to be 4-regular, and (R) gives χ_f ≤ (4 + 1 + 3)/2 = 4.
  * For |S| ≤ 7: every graph on ≤ 7 vertices with ω ≤ 3 has χ_f ≤ 7/2.

The two finite facts are exact atlas computations (`verifier/f037_joins_s5.py`: 844 graphs,
maximum 7/2, and maximum 5/2 when triangle-free). ∎

*Scope.* s = 4 reduces to a finite check, not yet run:

* the same reduction gives δ ≥ 5 and e(S) ≤ 2|S| + 6, so |S| ≤ 12;
* |S| = 12 forces 5-regularity, and (R) gives ≤ (5 + 1 + 4)/2 = 5;
* so the check is on ≤ 11 vertices.

s ≤ 3 is open.

## Supporting lemma (used in Theorem B)

**L1 (extension).** χ_f(G) ≤ max{χ_f(G − v), min(χ_f(G − v) + 1, d(v) + 1)}.

*Proof.* Make an optimal fractional colouring of G − v cover every vertex exactly once, by
shrinking sets. The sets meeting N(v) weigh ≤ d(v). Put v into the rest, up to weight 1, and add
{v} for any shortfall. ∎

Consequence used above: in a vertex-minimal graph with χ_f > k, every degree is > k − 1.

## Calibration (examples)

| set | Theorem A | Theorem B |
|---|---|---|
| **(a)** K₅ ∨ C₈² | not a line graph of any multigraph: in L(H) every neighbourhood is covered by 2 cliques, but an apex's neighbourhood contains C₈², which needs 3 (its cliques are triangles) | s = 5, value exactly 9: sharp |
| **(a)** K₁ ∨ C₁₆(1,2,6,7,8) | not a line graph: the apex's neighbourhood C₈² ⊠ K₂ needs ≥ 3 cliques | outside the scope (s = 1) |
| **(b)** 22 line graphs | roots have μ ≥ 4 (checked), so (i) is silent; they are exactly the (ii) list | — |
| **(b)** P | not a line graph (a claw at an A-vertex): P has vertex classes A, B₁, B₂, B₃ (size 2) and C₁, C₂, C₃ (size 6); A, B₁∪B₂∪B₃ and each C_i are cliques, and C_i ∼ A ∪ B_i. An A-vertex plus one vertex from each C_i is an induced K₁,₃ | — |
| **(c)** C₇ ⊠ K₄ = L(4·C₇) | μ = 4, so (i) is silent; it is excluded from the 22 by the triangle-free count | — |

## Known limits

* Theorem A(ii) rests on the (F32) and (F5) machine enumerations; **A(iii) rests on (F5) only**
  Both enumerations are independently re-derived (F32 twice).
* Theorem A says nothing about graphs that are not line graphs.
* The bound 9 in (iv) rests on (L5), machine-checked under (H2) and (H3). The bound 28/3 in (iii)
  does not use it.
* The (F32) and (F5) enumerations are Python code, re-derived independently but not
  machine-checked in Lean.

## Appendix: sharpness certificate for Theorem B

K₅ ∨ C₈² on vertices 0–12, with apexes 0–4 (the vertices of degree 12), split into two
edge-disjoint planar layers of 33 edges each. The two layers are a pair of triangulations, since
66 = 6·13 − 12.

Re-verified 2026-09-24 22:2x with networkx: both layers planar; edge-disjoint; union isomorphic to
K₅ ∨ C₈². Source: `population/satprop_f034-K5vC8sq_partition.json`.

* **Layer 1:** 0-1 0-3 0-5 0-11 1-2 1-3 1-4 1-5 1-6 1-7 1-8 1-12 2-3 2-6 2-8 2-10 2-12 3-7 3-8 3-9 3-10 3-11 3-12 4-7 4-8 4-9 5-11 5-12 6-12 7-9 8-9 8-10 11-12
* **Layer 2:** 0-2 0-4 0-6 0-7 0-8 0-9 0-10 0-12 1-9 1-10 1-11 2-4 2-5 2-7 2-9 2-11 3-4 3-5 3-6 4-5 4-6 4-10 4-11 4-12 5-6 5-7 6-7 6-8 7-8 9-10 9-11 10-11 10-12

---
*Exported from the authors' internal research record with light edits: internal cross-references,
per-model notes and the revision history were removed. The mathematics is unchanged.*
