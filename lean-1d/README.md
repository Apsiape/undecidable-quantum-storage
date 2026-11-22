# Lean proofs for the one-dimensional sparsity estimates

These Lean 4 files formalize the finite sparsity and witness-tree estimates shared by two papers:

* Douglas and Mghirbi, *An uncomputable noise diagram on the line and a finite-energy Gibbs diagram on the square lattice*, version 2.0.0, doi:10.5281/zenodo.24352353 (below: **[N]**): Definition 4.1, Lemma 4.2, the tools and raw-flag sum of Lemma 4.6, and 22 parameter inequalities;
* this paper, **Lemmas 12.1 and 12.2** (restricted witness trees and their probability; the effective radius-moment cutoff), the arithmetic of **Lemma 16.1** with its fidelity inputs supplied as hypotheses, and selected exponent calculations from **Lemmas 14.1 and 14.2**.

All 54 statements are proved with no `sorry` and no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The official Lean comparator accepts the solution against the frozen challenge.

## Scope

The formalization verifies the lattice sparsity definition and its basic properties, the disjoint-child witness construction and finite tree counts, and the independent-flag probability bounds of Lemma 4.2 of [N]. It also verifies the support-independence and bounded-overlap estimates underlying equation (4) of [N], conditional exponent bookkeeping, and the raw-flag nested-test sum in the first conclusion of Lemma 4.6 of [N]. For the quantum stencil model it verifies the probability estimate and threshold of Lemma 12.1 of this paper for independent elementary keys with finite stencils and chosen integer radius bounds; identification with the final physical circuit remains an application hypothesis. It verifies Lemma 12.2 with integer primitive-stencil radius bounds: its explicit cutoff ε_R(d,δ) is positive, is computable as a rational from ⌈d⌉ and δ (the executable `Q1.eRcut`), is at most ε_R0, and makes the clock moment summable with sum at most δ. It verifies the recursion and horizon arithmetic of Lemma 16.1. Its fidelity calculation assumes the failure probabilities, the union bound and the overlap inequality of that proof; the overlap inequality is established in the companion `lean/` library. It verifies selected identities and inequalities in the exponent calculations of Lemmas 14.1 and 14.2, listed in the table below. It additionally checks the listed 22 arithmetic parameter inequalities. It does not verify the painted-error conclusions or either cluster-tail conclusion of Lemma 4.6 of [N], general admission-rank packing (Lemma 12.3), the probability estimates of Lemmas 14.2 and 16.1, the automaton, its organization induction, or the physical compilation and main theorems.

## Files

| File | Role |
|---|---|
| `Flagship1D/Defs.lean` | Every definition and every statement, as a named `Prop` |
| `Flagship1D/Challenge.lean` | The same definitions and statements followed by the 54 theorems with `sorry` bodies (comparator format); imports only Mathlib |
| `Flagship1D/Stage1.lean`, `Stage2.lean`, `Stage3.lean`, `Stage4.lean` | The proofs |
| `Flagship1D/Solution.lean` | Imports the proofs; each theorem named in `Challenge.lean` has exactly the Challenge statement as its type |
| `Flagship1D/Audit.lean` | Re-checks each theorem against its statement and prints its axioms |
| `comparator.json` | The 54 theorem names and the permitted axioms; nanoda enabled |
| `scripts/check.sh` | Runs every check below and stops at the first failure |
| `scripts/export.sh`, `scripts/compare_exports.py`, `scripts/test_compare_exports.py`, `scripts/targets.txt` | Exports, the secondary export comparison and its self-test |
| `evidence/` | Logs and receipts of the recorded runs |

`Flagship1D` is the Lean namespace of the development.

## Build and check

The proofs use Lean `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`) and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; all dependencies are pinned in `lake-manifest.json`. The checks use the comparator built into Lake and the exporter and kernels bundled with this toolchain (`leanexport`, `leanchecker`, `nanoda_bin`). The comparator sandboxes its work with bubblewrap: put `bwrap` on `PATH` or set `COMPARATOR_BWRAP` to its full path. Run from this directory on Linux:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake comparator --config comparator.json
```

`lake exe cache get` downloads Mathlib's prebuilt files, so `lake build` compiles only the eight `Flagship1D` modules; the 54 `sorry` warnings come from `Challenge.lean` by design. The comparator ends with exit status 0 and these lines:

```text
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

To run everything (cache, build, comparator, axiom audit, fresh exports, `leanchecker` and `nanoda` replays, and the secondary export comparison):

```sh
scripts/check.sh
```

It writes its logs to `check-output/` (or `$CHECK_OUT`), exits with the status of the first failed step, and prints `ALL CHECKS PASS` only if every step passed. The axiom audit alone is `lake env lean -j1 Flagship1D/Audit.lean`; it prints 79 lines, one for each of the 54 theorems and for 25 supporting lemmas and satisfiability witnesses of the Lemma 12.2 and 16.1 statements. Each reads `depends on axioms: [propext, Classical.choice, Quot.sound]`, except three arithmetic statements (`num_ownerCollar`, `num_commonSpan`, `num_deficitConstant`) that use only `[propext, Quot.sound]` and `Q1.BR_pos`, which uses only `[propext]`. Its two `#eval` lines evaluate the cutoff of Lemma 12.2.

## Verification record

| Check | Result |
|---|---|
| Official comparator | `lake comparator --config comparator.json`: exit 0. All 54 theorems match `Challenge.lean`, only the permitted axioms occur, and the nanoda and Lean kernels accept the solution. [stdout](evidence/Comparator.stdout.log), [receipt](evidence/Comparator.receipt.json), [sandbox invocations](evidence/Sandbox.invocations.ndjson) |
| Negative controls | The comparator rejects the solution when `Classical.choice` is not permitted ("Illegal axiom detected") and against a challenge whose theorem `num_flankPass` is given another statement ("statement do not match"); nanoda rejects the challenge export (`sorryAx`). [status](evidence/Negative.status.txt) and the `Negative-*` logs |
| Full check run | `scripts/check.sh`: every step exit 0, `ALL CHECKS PASS`. [status](evidence/CheckAll.status.txt), [receipt](evidence/CheckAll.receipt.json) |
| Kernel replays of a fresh export | `leanchecker --from-export` accepts; `nanoda_bin` with the permitted-axiom list as a hard error exits 0. [leanchecker](evidence/Leanchecker.log), [nanoda configuration](evidence/nanoda.json), [export digests](evidence/EXPORT-DIGESTS.txt) |
| Axiom audit | 79 lines (the 54 theorems and 25 supporting declarations), only the standard axioms. [log](evidence/AxiomAudit.log) |
| Mathlib from cache | All 3122 jobs of the imported Mathlib modules were up to date before the build; no Mathlib module was compiled. [log](evidence/MathlibUpToDate.log) |
| Secondary export comparison | Custom comparison of the 54 target signatures, the exported Challenge dependencies and the exported Solution axioms. This is not an official comparator run and not an equivalent implementation; it keeps Lean's structured names (anonymous/str/num), hash-conses expressions exactly (modulo binder names and annotations, as Lean's expression equality does), rejects duplicate ids and declarations, and compares the whole exported Challenge closure. PASS, and it rejects both deliberately altered challenges. [log](evidence/SecondaryCheck.log), [self-test](evidence/SecondaryCheck.selftest.log) |
| Driver exit status | `scripts/check.sh` runs with `set -euo pipefail`, checks every step's exit status and verdict line, and prints `ALL CHECKS PASS` only after all of them succeeded. |

Tool digests are in [TOOLCHAIN-DIGESTS.txt](evidence/TOOLCHAIN-DIGESTS.txt); all files are listed with hashes in [MANIFEST.md](MANIFEST.md).

## Faithfulness table

Each row pairs a theorem `Flagship1D.name : Flagship1D.Statement` with the printed statement it formalizes. Lattice: `ℤ × ℤ` (site, time); `box a b L M = [a, a+L) × [b, b+M)`; a translate of `c·V^j` is `box a b (c·P^j) (c·T^j)`.

**Noise model.** Independent Bernoulli coordinates with possibly unequal rates p(k) bounded by u (respectively ε). Constant p gives the iid classical model; unequal deterministic rates include the quantum elementary-rate splice.

### Sparsity, Lemma 4.2 and Lemma 4.6 of [N]

| Lean theorem : statement | Printed statement | Differences in form |
|---|---|---|
| (definition) `Sparse` | [N] Definition 4.1: "A set is 0-sparse if it is empty. It is j-sparse if every translate Q of wV^j admits a translate J of 3wV^{j−1} such that (E∩Q)∖J is (j−1)-sparse." | Exact, by recursion on j, for E ⊆ ℤ×ℤ. |
| `sparseInheritedBySubsets : SparseInheritedBySubsets` | [N] after Definition 4.1: "Sparsity is inherited by subsets" | None. |
| `sparseImpliesNextSparse : SparseImpliesNextSparse` | [N] after Definition 4.1: "(j−1)-sparsity implies j-sparsity" | Indexed as j → j+1. |
| `fullBoxNotSparse : FullBoxNotSparse` | [N] after Definition 4.1: "A full V^j is never j-sparse." | Explicit hypotheses w ≥ 1, T ≥ 1, P ≥ 3w+2; `num_fullBoxHypothesis` shows P = 5·2^w satisfies the last. |
| `lemma_4_2_witness : Lemma_4_2_Witness` | [N] Lemma 4.2: "If the restriction to a full box of side vector 2wV^{j+1} fails (j+1)-sparsity, two disjoint full child boxes of side vector 2wV^j inside it fail j-sparsity. The child positions come from a deterministic list of at most (2P+3)(2T+3) boxes." | Explicit flush list of (2P−1)(2T−1) children at positions k·wP^j, l·wT^j, fixed before E and contained in the parent. |
| `lemma_4_2_pairCount : Lemma_4_2_PairCount` | [N] Lemma 4.2 proof: "at most D=8(P+2)²(T+2)² candidate pairs" | C(n,2) ≤ D for every n ≤ (2P+3)(2T+3). |
| `bjRecursion : BjRecursion` | [N] Lemma 4.2 proof: "b_0≤4w²u … b_{j+1}≤Db_j², and b_j≤D^{−1}(4Dw²u)^{2^j}≤D^{−1}u^{2^{j−1}} if u≤(4Dw²)^{−2}" | Solves the recursion for any nonnegative sequence satisfying the two displayed bounds; it does not derive them. |
| `lemma_4_2_probability : Lemma_4_2_Probability` | [N] Lemma 4.2: "for independent flags of rate u sufficiently small, the probability of j-nonsparsity on a prescribed fixed multiple of V^{j+1} is at most C_0 u^{c_0 2^j}, with C_0,c_0>0 independent of j, of the translate and of u", with the displayed bounds of its proof | (i) every doubled rank-j box, every u ≥ 0: D^{−1}(4Dw²u)^{2^j} (j = 0 gives 4w²u); (ii) ≤ D^{−1}u^{2^{j−1}} if u ≤ (4Dw²)^{−2}; (iii) every multiple m_x P^{j+1} × m_y T^{j+1} and translate: C_0 u^{c_0 2^j} with C_0 = (m_x P+1)(m_y T+1)/D and c_0 = 1/2. Derived from `witnessTreeProbability`; the recursion b_{j+1} ≤ D b_j² for the supremum is not stated separately, its solved bound is proved directly. |
| `meshRootCover : MeshRootCover` | [N] Lemma 4.2 proof: "A fixed multiple of V^{j+1} can be tested with a bounded cover by full rank-j boxes"; this paper, Lemma 12.1 proof: the mesh cover | Failure on a rectangle implies failure of the restriction to one doubled box of a mesh anchored at its corner. |
| `independentSelection : IndependentSelection` | [N] Lemma 4.6 proof: "Select at least L/(Δ_leaf+1) disjoint supports in each deterministic tree." | Finite graph with symmetric conflicts and degree ≤ D: a conflict-free subfamily t with \|s\| ≤ (D+1)\|t\|. |
| `productOnDisjointSupports : ProductOnDisjointSupports` | [N] Lemma 4.2 proof: "Disjoint children carry independent flags"; [N] Section 4.4: "products concern disjoint innovation supports" | Independent site σ-algebras (`iIndep`); events measurable in pairwise disjoint supports have product probability. |
| `treeBound : TreeBound` | [N] Lemma 4.6, equation (4): "the product bound on the selected supports followed by a union over trees is at most (Cα^{1/(Δ_leaf+1)})^{2^{i−j}}" | Abstract: trees given by their leaf sets, general L in place of 2^{i−j}; tree count, leaf measurability, degree bound and the leaf probability α are hypotheses. |
| `restrictedWitnessTrees : RestrictedWitnessTrees` | [N] Lemma 4.6 proof: "Iteration of Lemma 4.2 produces a binary tree with L=2^{i−j} disjoint leaf boxes of rank j"; this paper, Lemma 12.1 proof: restriction "to every ancestor at each node" | Root of rank m+r, leaves of rank m; every leaf fails m-sparsity on its box intersected with all ancestor boxes, the initial restriction being carried by F. |
| `witnessTreeShape : WitnessTreeShape` | same passages: 2^{i−j} leaves, disjoint leaf regions and leaf boxes | 2^r leaves with pairwise disjoint regions; with the flush placement each region is the full leaf box. |
| `witnessTreeCount : WitnessTreeCount` | [N] Lemma 4.6 proof: "at most C^{L−1} possible trees for fixed root"; this paper, Lemma 12.1 proof: "at most D_R^{N−1} geometric trees" | At most D^{2^r−1} trees, D = 8(P+2)²(T+2)². |
| `leafOverlapDegree : LeafOverlapDegree` | [N] Lemma 4.6 proof: "the intersection graph of the enlarged leaves has degree at most a fixed Δ_leaf" | Pairwise disjoint full doubled boxes enlarged by natural multiples a_x, a_y of the half-sides: Δ_leaf = (3+2a_x)(3+2a_y) − 1. Not the general clipped-region packing of Lemma 12.3. |
| `exponentBookkeeping : ExponentBookkeeping` | [N] Lemma 4.6 proof: "Choose D_s>12d_s+10 and M_s>max(8d_s,(Δ_leaf+1)(D_s+1)+2d_s) … For small p, (4) bounds raw-plus-short nonsparsity at i>j_s by p^{D_s 2^{i−j_s}}." | Conditional algebra: α ≤ K p^{M−2d} with M > (Δ+1)(D+1)+2d gives (Cα^{1/(Δ+1)})^{2^n} ≤ p^{D·2^n} when C K^{1/(Δ+1)} p ≤ 1. The leaf bound itself (painted events, scales, helpers) is not derived. |
| `nestedTestSumRaw : NestedTestSumRaw` | [N] Lemma 4.6: "the sum of the failure probabilities for one prescribed (j−1)-sparsity test in a fixed multiple of V^j at every rank j≥1 is less than 1/4, uniformly in their translations", for "raw flags alone at all sufficiently small fixed rates" | Raw flags only, one test per rank, arbitrary prescribed translations; explicit cutoff u ≤ (4Dw²)^{−2} and u < 1/(64C_0²). |

### Lemma 12.1 of this paper

| Lean theorem : statement | Printed statement | Differences in form |
|---|---|---|
| `conflictDegreeArea : ConflictDegreeArea` | Lemma 12.1 proof: "this conflict graph has degree at most Δ_R" | Disjoint regions in 2w×2w boxes, keys with integer representatives within natural radii: at most J_R − 1 conflicts. |
| `witnessTreeProbability : WitnessTreeProbability` | Lemma 12.1 proof: "Pr(failure) ≤ N_R D_R^{N−1} (A_R ε)^{N/J_R}" | Abstract independent Bool keys with rates ≤ ε, flags = OR over stencils of at most s keys; roots, trees, regions and the conflict degree are hypotheses; valid when 4w²s·ε ≤ 1. |
| `q1_l1 : Q1_L1` | Lemma 12.1: "For any prescribed protected rank-j W_0 test of width < w_R P_R^j and height < w_R T_R^j, its failure of (j−1)-sparsity has probability at most z_{R,j}(ε) = [C_R ε^{c_R}]^{2^{j−1}}, j ≥ 1", with D_R, N_R, A_R, J_R, Δ_R, c_R, C_R as displayed | The probability bound and threshold are formalized for arbitrary finite stencils with the printed hypotheses: positive integer geometry, an integer key bound s_R ≥ 1, nonnegative integer radii r_x, r_t, and independent keys with possibly unequal rates at most ε; each key has an integer site/time representative. Choose integer upper bounds when enumerating the final circuit; flooring physical site/macrodate coordinates preserves those bounds and the displayed constants. This conversion, enumeration of actual compiled stencils, and identification of the physical field with the product-key model are application steps, not formalized circuit results. |
| `q1_l1_threshold : Q1_L1_Threshold` | Lemma 12.1: "C_R ε^{c_R} ≤ 1/2 for 0 ≤ ε ≤ ε_R0", ε_R0 = A_R^{−1}(2N_R D_R)^{−J_R}, which "also ensures A_R ε ≤ 1" | Exact; assumes w, s ≥ 1. |

### Lemmas 12.2, 14.1, 14.2 and 16.1 of this paper

| Lean theorem : statement | Printed statement | Differences in form |
|---|---|---|
| `q1_l1_1 : Q1_L1_1` | Lemma 12.2: "For every real d ≥ 0 and every rational δ > 0 there is a rational ε_R(d,δ) > 0, depending on d only through ⌈d⌉ and computable from ⌈d⌉ and δ, such that Σ_{j≥1} N_clk (1+r_{R,j})^d √(z_{R,j}(ε)) ≤ δ for every 0 ≤ ε ≤ ε_R(d,δ)" | The cutoff is the proof's ε_R(d,δ) with the least j_*, computed from ⌈d⌉ (`Q1.eRcut`, executable, into ℚ); the proof's θ_R = min(1/4, (δ/K_R)²) is `Q1.qR`. Also ≤ ε_R0; summability stated. Integer primitive-stencil radii r_x, r_t and positive integer geometry; the moment radii are any reals 0 ≤ r_{R,j} ≤ C_clk B_R^j. |
| `q1_l1_1_uniform : Q1_L1_1_Uniform` | proof of Lemma 12.2: "Replace d by its integer ceiling d'" | One natural d' serves every real 0 ≤ d ≤ d'. |
| `q1_l18_recursion : Q1_L18_Recursion` | Lemma 16.1: "If 0 < b_* ≤ 1/(4A_pair) and C_rec δ ≤ b_*/4, then u_i ≤ b_* 2^{-i} for all i ≥ 0" | u_i ≥ 0, as printed; any q ∈ [0, 1/4]. |
| `q1_l18_horizon : Q1_L18_Horizon` | Lemma 16.1: "If k is largest with 4C_cone(T_q^k+P_q^k+1) ≤ L, H = T_q^k, and 2 ≤ P_q ≤ T_q, then L < 12 C_cone T_q H, with c_1 = 1/(12 C_cone T_q), c_1 L < H ≤ D_layer H" | "Largest" as `IsGreatest`; adds k ≥ k_0 for every k_0 meeting the cutoff and t ≤ D_layer H for every t ≤ ⌊c_1 L⌋. |
| `q1_l18_fidelity : Q1_L18_Fidelity`, `q1_l18_fidelity_at_times : Q1_L18_FidelityAtTimes` | Lemma 16.1: "for k ≥ k_0 the nominal-rate completion decoder has entanglement fidelity at least 1 − 1/128 − 1/32 = 123/128 ≥ 15/16 = 120/128 at every integer elementary time 0 ≤ t ≤ ⌊c_1 L⌋" | Conditional arithmetic form: the helper failure (< 1/128), at most C_top top tests each of probability ≤ u_k, the union bound and the overlap step are hypotheses (the overlap step is `QuantumScope.good_event_fidelity_union` in `lean/`). Also F ≥ 1 − p_help − C_top b_* 2^{-k} and F ≥ 1 − p_help − 1/32 (proof of Corollary 1.1). |
| `q1_l18_k0`, `q1_l18_rank_exists` | Lemma 16.1: "Choose k_0 ≥ 1 with C_top b_* 2^{-k_0} ≤ 1/32"; proof: "a computable sufficient size cutoff ... makes k ≥ k_0 for all larger L" | k_0 = ⌈log₂ C_top⌉ + 3 works for b_* ≤ 1/4; the largest rank exists once the cutoff is met. |
| `q1_l12_ledger`, `q1_l12_step1` | Lemma 14.2, Steps 1, 3, 4, 5, 7: h_red + 1 − C_pref = M_l + 6; C_pref > 2(b_refresh+6)+4; b_refresh > 20; M − 2ρ ≥ 2(Δ_ad+1)D + 20; M/2 − d_mom ρ > 0; D > d_mom ρ; the Step 1 band bound | For every R_geom and d_mom; the admission-rank bounds, Step 7's rational-power conditions and the range bounds (14.7)-(14.9) are not formalized. |
| `q1_l11_ledger` | Lemma 14.1: (s_read+1)/4 = M_s + 21.5, b_refresh − 7 ≥ M_s + 13, v_rep − 8 = M_s + 12, (m_ch+1)/20 = M_l + 20.1, (m+3)/(8(m+2)) < 1, ν_2(2^n(2J_pad+1)) = n, s_read and m_ch odd | Exact. |

### Parameter inequalities of [N]

Parameters as in [N] Section 3 and Appendix A: q = w², A = w³, B = 128q, v = w⁴, P_0 = 2^w, P = 5P_0, H_0 = 2q+2, d_0 = (2A+4)H_0, d_1 = q d_0, m = ⌊w/5⌋, d = 4w+8, M = 128d, Δ = 1024q, t_c = 2d+9q+40, N = 200A d_1, D_tr = 50A d_1 + (6N+4w^6+21)(5d_0+1) + w^6 + 2d_0 + 20. Each statement holds for every natural w at the threshold shown.

| Lean theorem | Printed inequality and location in [N] | Threshold |
|---|---|---|
| `num_cavityGain` | 2(B−20)−(B+30q+40) = 98q−80 > 0 (Lemmas 5.7 and 5.8) | w ≥ 10^10 |
| `num_flankPass` | q+d+32 < B (Lemma 5.6) | w ≥ 10^10 |
| `num_flankResponseTime` | d+4q+14+2d_0 < w^6 (Lemma 5.6) | w ≥ 10^10 |
| `num_clearanceTime` | t_c < 5H_0 (Lemma 5.7) | w ≥ 100000, as printed |
| `num_responseTime` | 2d_0+10H_0 < w^6 (Lemmas 5.7 and 5.8) | w ≥ 100000, as printed |
| `num_cavityLength` | q+2d+55 ≤ 30q+40 (Lemma 5.7) | w ≥ 10^10 |
| `num_woundBand` | 2B+40q+40 < 0.2A (Lemmas 5.8 and 5.10) | w ≥ 10^10 |
| `num_seedRatio` | 3Δ/A = 3072/w < 0.031 (Lemma 5.9) | w ≥ 100000, as printed |
| `num_seedSpacing` | d_1 = q(2A+4)(2q+2) > 4w^7, hence w^6 < d_1 (Lemma 5.9) | w ≥ 100000 |
| `num_seedCount` | 8(L+2)+5 < 100A with L = 3A+3Δ (Lemma 5.9) | w ≥ 100000 |
| `num_epochCost` | (M+1)/(M−4d−1) < 2 and (⌈(20A+2M)/(M−4d−1)⌉+2)(M+1) ≤ 100A+4(M+1) (Lemma 5.10) | w ≥ 10^10 |
| `num_transportMargin` | 2(D_tr+10A+10q)+d < P_0/2 and 12A+4q+D_tr+10A+10q < P_0/2 (Lemma 5.10) | w ≥ 10^10 |
| `num_rearWall` | Proof of Lemma 5.4, localization paragraph: 3vd_0+2w^6+12d_0+20 < P/10, proved as arithmetic for every natural w ≥ 10^10. | w ≥ 10^10 |
| `num_ownerCollar` / `num_commonSpan` | Proof of Lemma 5.4, localization paragraph, and Appendix A: the two products, 608 < ⌊w/5⌋, and 3w+2⌊w/5⌋+4+1216 < d are proved. The geometric query enumeration is not formalized. | w ≥ 10^10 |
| `num_satelliteWidth` | d+10 < q (Lemma 5.12) | w ≥ 10^10 |
| `num_deficitConstant` | w > 100(C+1000), C = 2,000,000 (Lemma 5.16); the deficit constant itself is not proved | w ≥ 10^10 |
| `num_recruitment` | 5q+2d+12 < 4(2q+2) (Lemma 5.19) | w ≥ 10^10 |
| `num_advanceDebit` | d+4(q+20) < 5q < B−10 (Lemma 5.23, Appendix A) | w ≥ 10^10 |
| `num_endpointException` | d+q+42 < 2q (Appendix A) | w ≥ 10^10 |
| `num_endGap` | Δ < 16B+2d+24 < 3Δ (Appendix A) | w ≥ 10^10 |
| `num_fullBoxHypothesis` | P = 5·2^w ≥ 3w+2, the bridge to `fullBoxNotSparse` | all w |

**Numerical scope.** All 22 listed arithmetic claims hold at their displayed thresholds. This does not certify the interpreter allowance, clock duration T or its asymptotics, counted geometric budgets, or every sufficiently-large-w requirement of the construction.

### Not covered

The supremum recursion b_{j+1} ≤ D b_j² as a separate statement; the painted-set sum and both cluster-tail conclusions of Lemma 4.6 of [N], including the weighted ball sum (5); Lemma 12.3 of this paper, the probability content of Lemmas 14.2 and 16.1 (Steps 3, 5 and 7 analytics, the recursion's derivation, the coupling); the automaton, its organization induction, the physical compilation and the main theorems.
