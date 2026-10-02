# P-009 — Every biplanar graph on n vertices has an independent set of size > 2n/21

**Status:** proven. **Not peer-reviewed.** The proof went through three rounds of adversarial review by
AI models from three different model families, and every round returned it correct. The last round
was blind: the reviewer saw only the mathematics. This is cross-model review, not peer review.

**Answers:** Král', Barbados Graph Theory Workshop 2018, **Problem 4**, verbatim: *"Show for some
c > 1/12 that every n-vertex biplanar graph has an independent set of size at least cn."* Szeider
(arXiv:2609.28102, 23 Sep 2026) still lists it as open.

**Rests on:** one recent theorem, Abiad–Kumar–Pragada, arXiv:2609.00210 (31 Aug 2026, v1,
**unrefereed**). Its proof is re-derived in full below, so this file is self-contained. The
**content** is a short corollary of their theorem. What is new is the observation that it answers
Král's question.

**Novelty:** documented searches on 2026-09-24 and 2026-10-02 found no source that connects the
Abiad–Kumar–Pragada theorem to biplanar or planar graphs; their paper never mentions planarity. The
searches covered zbMATH Open, arXiv, Semantic Scholar and OpenAlex citations, Zenodo and GitHub. See
the README for their limits.

## Statement

**Theorem.** Every biplanar graph G on n ≥ 1 vertices with e edges satisfies

  α(G) ≥ Σ_v 2/(d(v) + c(v) + 1) ≥ 2n²/(2e + 9n) > 2n/21,

where c(v) is the order of a largest clique containing v. Since e ≤ 6n − 12 for n ≥ 3, this gives
α(G) ≥ 2n/(21 − 24/n).

So the **infimum** of α(G)/|V(G)| over biplanar graphs G lies in **[2/21, 2/17]**. This is a
class-level statement: an individual biplanar graph can have a larger ratio, for example an
edgeless graph has ratio 1. The upper end comes from
the known biplanar graphs with α = 2 on 17 vertices (Gethner–Sulanke Open Problem 2 asks
whether 2/17 can be beaten). Before this, the best lower end was 1/12, from 11-degeneracy.

## Proof

### Step 1: the localized Caro–Wei bound

This is Abiad–Kumar–Pragada, Thm 3.1, which proves a conjecture of Brause–Randerath–Rautenbach–
Schiermeyer (2016). **For every graph G, α(G) ≥ Σ_v 2/(d(v) + c(v) + 1).**

**Lemma 1 (their Thm 2.2).** Let S be the simplex {x ≥ 0 : Σ x_v = 1}, A the adjacency matrix and
C = diag(c(v)). For every x ∈ S,

  Q(x) := xᵀ(I + C + A)x ≥ 2/α(G).

*Proof.*

1. **A minimiser.** Let z minimise Q (continuous) over the compact set S, and write
   f(v) := (c(v) + 1)z_v + Σ_{u ∈ N(v)} z_u = ((I + C + A)z)_v.
2. **f is constant on supp(z).** Suppose u, v ∈ supp(z) with f(u) > f(v). Put
   y = z + ε(e_v − e_u). Then Q(y) − Q(z) = ε[2(f(v) − f(u)) + ε(c(u) + c(v) + 2 − 2A_uv)], and the
   bracket is negative for 0 < ε small (and ε ≤ z_u, so y ∈ S), contradicting minimality. Hence
   f(u) = Σ_w z_w f(w) = Q(z) for every u ∈ supp(z).
3. **A good independent set.** Among the maximum independent sets of G[supp(z)], pick U
   maximising z(U).
   * Every w ∈ supp(z) ∖ U has a neighbour in U, by maximality.
   * Let X_u = {w ∈ supp(z) ∖ U : N(w) ∩ U = {u}} be the private neighbours of u.
4. **X_u is small.** X_u is a clique: two non-adjacent members could replace u and enlarge U.
   X_u ∪ {u} is a clique too, so |X_u| ≤ c(u) − 1.
5. **Private neighbours are light.** For w ∈ X_u, (U ∖ u) ∪ {w} is again maximum in G[supp(z)].
   By the choice of U, z_w ≤ z_u. Hence Σ_{w ∈ X_u} z_w ≤ (c(u) − 1)z_u.
6. **Summing.** Use step 2 (f(u) = Q(z) on U ⊆ supp(z)). Every w ∈ supp(z) ∖ (U ∪ X) has
   ≥ 2 neighbours in U, and z(U) + z(X) + z(rest) = 1. So
   |U|·Q(z) = Σ_{u∈U} f(u)
            = Σ_{u∈U} (c(u) + 1)z_u + Σ_w |N(w) ∩ U| z_w
            ≥ Σ_{u∈U} (c(u) + 1)z_u + Σ_{u} Σ_{w∈X_u} z_w + 2z(rest)
            = 2 + Σ_{u∈U} [(c(u) − 1)z_u − Σ_{w∈X_u} z_w]
            ≥ 2.
7. **Conclusion.** Since |U| = α(G[supp(z)]) ≤ α(G), we get Q(x) ≥ Q(z) ≥ 2/α(G). ∎

**Lemma 2 (their Thm 3.1).** α(G) ≥ Σ_v 2/(d(v) + c(v) + 1).

*Proof.*

1. Put x_v := 1/(d(v) + c(v) + 1) > 0. Lemma 1 applied to x/‖x‖₁ gives xᵀ(I + C + A)x ≥ 2‖x‖₁²/α(G).
2. By 2x_u x_v ≤ x_u² + x_v² on each edge:
   xᵀ(I + C + A)x ≤ Σ_v (c(v) + 1)x_v² + Σ_{uv∈E}(x_u² + x_v²) = Σ_v (d(v) + c(v) + 1)x_v² = ‖x‖₁.
3. Hence α(G) ≥ 2‖x‖₁. ∎

### Step 2: the biplanar corollary

G is biplanar, so it contains no K₉: thickness(K₉) = 3 (Battle–Harary–Kodama 1962; Tutte 1963).
Euler alone does not exclude K₉, since 36 ≤ 42. Hence c(v) ≤ 8, and every term satisfies
2/(d(v) + c(v) + 1) ≥ 2/(d(v) + 9).

The function t ↦ 2/(t + 9) is convex on t ≥ 0. By Jensen, with d̄ = 2e/n,

  Σ_v 2/(d(v) + 9) ≥ 2n/(d̄ + 9) = 2n²/(2e + 9n).

For n ≥ 3, Euler on the two planar layers gives e ≤ 6n − 12. So d̄ < 12 and
α(G) ≥ 2n/(21 − 24/n) > 2n/21. For n ≤ 2, α ≥ 1 > 2n/21. ∎

*Euler-only fallback.* Without the thickness of K₉, Euler still forces
C(m, 2) ≤ 6m − 12 for a K_m in G with m ≥ 3, i.e. m ≤ 10. (Cliques with m ≤ 2 satisfy c ≤ 10
trivially.) That gives c(v) ≤ 10 and α > 2n/23. Since
2/23 > 1/12, Král's question is answered even without BHK/Tutte.

*Small orders.* The bound gives α ≥ 3 once n² − 21n + 24 > 0, i.e. for n ≥ 20. Szeider's
Corollary 4 gets n ≥ 19 by computer.

## Remarks and limits

* **Hall ratio.** The bound holds for every subgraph, so max_{H ⊆ G} |H|/α(H) < 21/2 for every
  biplanar G.
* **It does NOT bound χ_f below 12.** χ_f needs the weighted version: α_w ≥ w(V)/t for every
  weight w. The weighted form of the localized Caro–Wei bound is Kelly–Postle's local fractional
  Reed conjecture, which is open (Abiad et al. §1.1).
  * The conjecture AR, χ_f ≤ (mad + 1 + ω)/2 (not claimed here; stated for context), is implied by Kelly–Postle's Conjecture 1.14
    (JCTB 2020, arXiv:1911.02672), χ_ℓ ≤ ⌈(mad + 1 + ω)/2⌉ (even its χ form suffices). Here is the
    argument:
    1. Apply the conjecture to the clique blow-up G[K_t]. Using a fractional orientation of G
       with in-degree ≤ mad/2, mad(G[K_t]) ≤ t(mad(G) + 1) − 1; and ω(G[K_t]) = tω.
    2. So χ_t(G) = χ(G[K_t]) ≤ ⌈t(mad + 1 + ω)/2⌉.
    3. Since χ_f = lim χ_t/t, the ceiling disappears in the limit.
  * The theorem above gives an unweighted analogue of AR, in the form n/α ≤ (d̄ + 1 + ω)/2. It is an
    analogue, not an equivalent: AR uses mad(G) and χ_f(G), and no equivalence is claimed.
* **Dependence on an unrefereed preprint.** The proof of Lemma 1 is reproduced above and was
  checked line by line. The only non-trivial step is step 6, whose accounting was re-derived
  independently.
* **Machine sanity checks** (`verifier/f037_kral_check.py`):
  * the localized bound was never violated on 2,000 random graphs with n ≤ 14 (exact α);
  * it was never violated on 29 calibration graphs, or on Patil's public corpus of 166 biplanar
    graphs (GitHub Volkopat/earth-moon-biplanar; pass its directory as the script's argument);
  * the smallest α/n on those graphs is 2/19, above 2/21.

  These checks are evidence, not proof.
* **What this method can and cannot give.** The bound tends to 2/21 as n → ∞.
  * Equality in Lemma 2 alone is common (K₂ and every complete graph attain it).
  * Equality in the **whole relaxed chain** at 2n/21 would need c(v) = 8 everywhere and all
    degrees equal to 12, i.e. e = 6n. That contradicts e ≤ 6n − 12, as the finite-n form
    already shows.
  * None of this says the true infimum of α/n over biplanar graphs exceeds 2/21. Better control of
    c(v) near degree 12 is one possible route to a larger constant, not the only one.

---
*Exported from the authors' internal research record with light edits: internal cross-references,
per-model notes and the revision history were removed. The mathematics is unchanged.*
