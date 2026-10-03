# earth-moon-line-graphs

Two results on the **Earth–Moon problem**: the chromatic number of biplanar (thickness-2)
graphs, open since Ringel 1959. The known bounds are 9 ≤ χ ≤ 12.

1. **Every biplanar line graph is 9-colourable** (P-008). If H is a loopless multigraph and its line
   graph L(H) is biplanar, then χ_f(L(H)) ≤ 9 and χ(L(H)) ≤ 9. So no line graph can be a
   10-chromatic biplanar graph. The classical candidates C₇⊠K₄ and C₅⊠K₄ − v are line graphs (of
   multigraphs on a 7-cycle and a 5-cycle). The proof reduces the statement to 22 specific graphs on
   28 vertices, and **all 22 are proved non-biplanar by machine-checked Lean 4 theorems** in this
   repository.
2. **Every biplanar graph on n vertices has an independent set of size > 2n/21** (P-009). This
   answers Král's Problem 4 from the Barbados Graph Theory Workshop 2018 ("show for some c > 1/12
   that every n-vertex biplanar graph has an independent set of size at least cn"). The proof is a
   short corollary of a recent theorem of Abiad, Kumar and Pragada (arXiv:2609.00210). It does not
   bound the fractional chromatic number.

This is a research record, not a refereed paper. Every claim below carries its verification
status. **Nothing here has been peer-reviewed.**

Archived on Zenodo: **[10.5281/zenodo.23113159](https://doi.org/10.5281/zenodo.23113159)** (all versions;
v1.0.0 is [10.5281/zenodo.23113160](https://doi.org/10.5281/zenodo.23113160)). The earlier deposit on the
α ≤ 2 route is [10.5281/zenodo.22242268](https://doi.org/10.5281/zenodo.22242268).

## Claims

| # | Statement | Status |
|---|---|---|
| P-008 A(i) | L(H) biplanar and every edge multiplicity ≤ 3 ⇒ χ_f(L(H)) ≤ 9; multiplicity ≤ 2 ⇒ χ_f ≤ 8 (sharp: K₈) | Proven (short arithmetic from Edmonds' matching polytope and Euler) |
| P-008 A(ii) | χ_f(L(H)) > 9 ⟺ L(H) contains one of 22 explicit line graphs on 28 vertices | Proven, using two machine enumerations ((F32), (F5); Python, each re-derived independently) |
| P-008 A(iii) | Unconditionally, χ_f(L(H)) ∈ [0, 9] ∪ {28/3} for biplanar L(H) | Proven (uses (F5) only) |
| Lean | **Each of the 22 graphs is not biplanar** | **Machine-checked in Lean 4** (kernel + `native_decide`), 22 theorems; see below |
| **P-008 A(iv)** | **Every biplanar line graph of a loopless multigraph has χ_f ≤ 9 and χ ≤ 9** | Proven: A(ii) + the Lean theorems + Goldberg–Seymour (for χ) |
| P-008 B | K_s ∨ H biplanar with s ≥ 5 ⇒ χ_f ≤ 9, sharp: **K₅ ∨ C₈² is biplanar with χ_f = 9**, a biplanar graph whose fractional chromatic number reaches the best known chromatic number | Proven (finite checks by exact computation; explicit two-layer partition in the proof file) |
| **P-009** | **Biplanar ⇒ α ≥ Σ_v 2/(d(v) + c(v) + 1) ≥ 2n²/(2e + 9n) > 2n/21**; so the infimum of α/n over biplanar graphs lies in [2/21, 2/17] | Proven (corollary of Abiad–Kumar–Pragada, whose proof is reproduced and checked in the file) |

**Review:** both proof files went through three rounds of adversarial review by AI models from
three different model families. No round found a gap in any theorem or lemma. Round 1 found minor
defects in wording and in remarks, which were fixed. The third round was blind: the reviewer saw
only the mathematics, not earlier verdicts. This is cross-model AI review: useful hygiene, **not
peer review**.

## The Lean theorems (`lean/`)

For each of the 22 graphs G there is a theorem `Biplanar.A4M<i><r>.not_biplanar` (i = 00…21):

```lean
theorem not_biplanar (planar : List Biplanar.Edge → Prop)
    (H2 : ∀ (S : List Biplanar.Edge) (c : Biplanar.KurCert), c.valid S = true → ¬ planar S)
    (H3 : Biplanar.IsoInvariant G planar) :
    ¬ Biplanar.Biplanar planar G
```

* `Biplanar planar G` says that some 2-colouring of G's edge list has both colour classes `planar`.
* `c.valid S` checks that c exhibits a subdivision of K₅ or K₃,₃ inside S.
* `IsoInvariant` says that `planar` does not depend on vertex labels.
* Ordinary planarity satisfies (H2), by the elementary direction of Kuratowski's theorem, and (H3).
  So each theorem says that G is not biplanar.

**How the theorems are proved.** Each proof is a Lean-checked LRAT refutation (via
[LRAT-Catcher](https://github.com/leansolving/lrat-catcher)) of a CNF formula made of:
* Kuratowski witness clauses, each certified by `KurCert.valid`;
* lexicographic symmetry-breaking clauses, proved sound in `Biplanar/Sym.lean` from (H3).

The six heaviest graphs are split into cubes, between 16 and 22 per graph. A separate checked cover
certificate shows that the cubes exhaust every assignment.

**Trust base:** the Lean kernel, the Lean compiler (`native_decide`), LRAT-Catcher and the four
core files `lean/Biplanar/{Basic,SymDefs,Sym,Lift}.lean`.

| route | instances |
|---|---|
| one formula per graph | A4M00, 01, 02, 03, 05, 06, 08, 10, 14, 15, 16, 17, 18, 19, 20, 21 |
| fixed 16-cube split | A4M07S, A4M13S (and A4M14S, a second certificate for member 14) |
| per-cube search, adaptive split | A4M04C (22 cubes), A4M09C, A4M11C, A4M12C (18 each) |

`verifier/f038_a4_audit.py` checks every instance **independently of the pipeline that produced
it**:

* **Right graph.** The multigraph in the Lean file equals the i-th member of a fresh recompute of
  the enumeration, and the multigraph of the original solver run. G ≅ L(M) is checked by
  networkx, not by the solver's code.
* **Right statement.** The statement is verbatim the one above. There is no
  sorry/axiom/unsafe/macro/notation, and no `set_option` other than `maxHeartbeats`.
* **Real build.** The build log shows success with no error, and the axioms used are only
  propext, Classical.choice, Quot.sound and `native_decide` auxiliaries.
* **Right data.** The witness files match their SHA-256 in each MANIFEST.

Result: **22/22 members covered, 0 failing**. `verifier/f038_a4_audit_selftest.py` breaks one
artefact at a time (17 mutants: wrong graph, weakened statement, smuggled axiom, edited witness
file, …) and checks that the audit catches each one.

## Verify it yourself

**Requirements:**
* Python ≥ 3.12 with `networkx` and `python-sat` (1.9.dev15 was used);
* for the Lean rebuild: [elan](https://github.com/leanprover/elan) (the toolchain is pinned, Lean
  v4.30.0) and [CaDiCaL](https://github.com/arminbiere/cadical) 3.0.1 on `PATH`;
* `xz`.

```sh
sh tools/unpack_witnesses.sh                  # restores lean/data/*/w*.txt (2.9 GB) from data/witnesses/

python verifier/f038_a4_audit.py              # the audit above: 22/22, 0 failing (~30 s)
python verifier/f038_a4_audit_selftest.py     # 19/19: the audit catches every mutant

# Regenerate all 128 certified formulas from the Lean sources + witness files and compare
# them byte for byte with the SHA-256 recorded at certification time (about 10 min, no solver):
python tools/rebuild.py --all --check-cnf

# Rebuild a Lean theorem end to end: formula, CaDiCaL, lake build, axiom check (a few minutes
# the first time, when lake fetches LRAT-Catcher and builds the core):
python tools/rebuild.py A4M01 --check-cnf --solve --build
# All of them: hours on one core (CaDiCaL up to ~20 min per formula); a cube leaf's
# `lake build` needs up to ~6 GB of memory:
python tools/rebuild.py --all --check-cnf --solve --build --lean-jobs 2
```

The finite facts of the written proofs:

```sh
python verifier/f032_enumerate.py && python verifier/f032_analyse.py   # 7-vertex roots → 56 (minutes)
python verifier/f033_line_graph_route.py      # → 23 after hereditary Euler, containment, triangle-free count (~1 min)
python verifier/f034_hereditary_trifree.py    # → 22 (exact MaxSAT; ~35 min)
python verifier/f034_a4_line_graph_sat.py --list --recompute   # prints the 22 (the A4 list)
python verifier/f037_k2check.py               # fact (F5): all 157 five-vertex roots die (~80 s)
python verifier/f037_theoremA_checks.py       # Lemma A1 vs exact LP, Lemma A2 identity, A(i) arithmetic
python verifier/f037_lemma_tests.py           # chi_f = 28/3 on the 22, and other lemma checks
python verifier/f037_joins_s5.py              # the finite facts of Theorem B
python verifier/f037_kral_check.py [CORPUS_DIR]   # P-009 sanity checks (optionally on Patil's corpus)
```

**How the certificates were produced.** The original non-biplanarity runs (SAT with a lazy planarity
propagator, `verifier/f034_a4_line_graph_sat.py`) and the certification pipelines are included as a
record:
* `verifier/f034_a4_certify.sh`;
* `verifier/a4_split_certify.py`;
* `verifier/cube_search_certify.py`;
* `verifier/lean_static_resolve.py`, `lean_cnf_writer.py` and `lean_split_modules.py`.

Their logs are in `population/`. They expect the layout of the internal repository and are not
needed for verification: the Lean build re-checks everything.

## Provenance: read this before judging

This work was produced by an **AI research framework** directed and overseen by a human who is not
a professional mathematician. The framework runs long-horizon AI research sessions, checks every
claim by machine, runs adversarial review rounds across models, and documents its literature
searches. Choosing the questions and directing the framework is part of the work. AI-produced
mathematics warrants extra scrutiny; that is why every verification script, certificate and log is
published.

The proof files were exported from the internal research repository with light edits: internal
cross-references, per-model attribution notes and the revision history were removed, and the
mathematics is unchanged. The same applies to three code comments and two comments in
`lean/Biplanar/SymDefs.lean`; no definition or proof changed.

## Novelty, stated honestly

Documented searches on 2026-09-24 and 2026-10-02 found **none of the claims above** in the
literature. They covered:
* zbMATH Open, arXiv (every math.CO/cs.DM/cs.LO/cs.CG/cs.AI paper submitted or revised in the
  three weeks before 2026-10-02);
* Semantic Scholar and OpenAlex forward citations, Crossref;
* Zenodo, GitHub, the Epoch AI problem page, MathOverflow and the web.

**Limits:** MathSciNet and GitHub code search were not used. Some surveys were not read at source:
Gethner 2018, Gethner–Sulanke 2009 and Hutchinson 2016.

**Closest prior work:**
* Szeider (arXiv:2609.28102: α ≤ 2 ⇒ 9-colourable, Lean + SAT);
* Kirchweger–Scheucher–Szeider (SAT 2023: C₅⊠K₄ − v is not biplanar);
* 2026 preprints showing C₇⊠K₄ is not biplanar (Patil, Bastian, Beasley, Szeider, Park); P-008
  implies this, and the non-biplanarity of C₅⊠K₄ − v, as special cases;
* Abiad–Kumar–Pragada (arXiv:2609.00210), on which P-009 rests;
* Kelly–Postle (local and fractional versions of Reed's conjecture);
* Albertson–Boutin–Gethner 2011 (fractional colourings of thickness-two graphs).

Some of this may be known, or easy enough that nobody wrote it down. Corrections are welcome and
will be recorded.

**A correction to the earlier deposit (doi:10.5281/zenodo.22242268).** Its README reported that
searches had found none of its results in the literature. Searches made afterwards found the
following.

| Result | Found | Date relative to our deposit |
|---|---|---|
| P-004 (the four C₅ blow-ups) | Trivedi, Zenodo 2026 | earlier |
| P-005 | a one-line proof by the triangle-free count (Trivedi, Zenodo 2026) | earlier |
| P-006 for 14–16 vertices | Santos, Zenodo 2026 | earlier |
| P-003 | the same argument in Szeider, arXiv:2609.28102 | later |
| P-006 as a whole | the same argument in Szeider, arXiv:2609.28102 | later |

## Contact

Ivan Spogreev. Questions and corrections: please open an issue on this repository.

License: MIT (see LICENSE).
