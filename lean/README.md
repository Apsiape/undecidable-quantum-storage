# Lean proofs for Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers

These proofs accompany *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*, version 3.1.0.

| Paper result | Lean declaration |
|---|---|
| Lemma 6.5, for every positive j | `QuantumScope.iteration_extension` |
| Lemma 6.6, the Bell-sharing bound | `QuantumScope.bell_sharing_bound` |
| Lemmas 6.5 and 6.6, the bound 1/2 + 2^(-j-1) | `QuantumScope.iterated_cloning_bound` |
| Theorem 6.7, the conditional abstract form | `QuantumScope.uniform_forgetting` |
| Theorem 8.2, conditional window certification, the abstract form of Theorem 8.3 | `CertificationScope.abstract_window_certification` |
| Conditional form of (2.3), for round or layer channels with the stated replacement decomposition and weight at least p | `QuantumScope.replacement_ceiling_pow`, `QuantumScope.replacement_ceiling` |
| Conditional layer estimate under the same hypothesis with p > 0, implying τ ≤ log(6/5)/p < 1/p and hence (10.2) and the bound in Section 18 | `QuantumScope.replacement_lifetime_layer` |
| The overlap step in the proof of Lemma 16.1 | `QuantumScope.good_event_fidelity_union` |

The helpers `QuantumScope.equalMarginalExtension_comp`, `QuantumScope.replacement_fidelity`, `QuantumScope.replacement_lifetime`, `QuantumScope.replacement_eventually` and `QuantumScope.good_event_fidelity` are also frozen in `Challenge.lean`.

The Bell-sharing proof applies to every positive output count, finite-dimensional CPTP encoder and common decoder. The certification theorem takes the physical storage and forgetting bounds as hypotheses. The conditional forgetting theorem likewise assumes the extension and the replacement decomposition; a full replacement is a convex decomposition ρ ↦ q Tr(ρ) σ + (1-q) Φ(ρ) of the layer channel with Φ CPTP. [Formalization scope](SCOPE.md) · [Theorem 8.2 in LaTeX](docs/PRINTED-STATEMENT.tex)

## Build and check

Appendix J uses Lean `leanprover/lean4:v4.35.0` and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. All dependencies are pinned in `lake-manifest.json`. With the pinned toolchain installed, run from this directory. The cache download is optional.

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M5000 Solution.lean
```

The expected axiom output is

```text
'CertificationScope.abstract_window_certification' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.bell_sharing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.equalMarginalExtension_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.iteration_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.iterated_cloning_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.replacement_fidelity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.replacement_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.replacement_ceiling_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.replacement_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.replacement_lifetime_layer' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.replacement_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.uniform_forgetting' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.good_event_fidelity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumScope.good_event_fidelity_union' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Append these lines to separate copies of `Challenge.lean` and `Solution.lean` in this directory.

```lean
#check @QuantumScope.bell_sharing_bound
#check @CertificationScope.abstract_window_certification
#check @QuantumScope.equalMarginalExtension_comp
#check @QuantumScope.iteration_extension
#check @QuantumScope.iterated_cloning_bound
#check @QuantumScope.replacement_fidelity
#check @QuantumScope.replacement_ceiling
#check @QuantumScope.replacement_ceiling_pow
#check @QuantumScope.replacement_lifetime
#check @QuantumScope.replacement_lifetime_layer
#check @QuantumScope.replacement_eventually
#check @QuantumScope.uniform_forgetting
#check @QuantumScope.good_event_fidelity
#check @QuantumScope.good_event_fidelity_union
```

Run `lake env lean -j1 -M5000` with each copy’s filename and compare the printed declaration types with `Challenge.lean` and the paper. The fourteen `sorry` bodies in the frozen challenge expose the statements. The verified proofs are imported by `Solution.lean`.

## Comparator

The [Lean comparator](https://github.com/leanprover/comparator) mechanically compares all fourteen proved statements and their definitions against the frozen, Mathlib-only `Challenge.lean`. With a comparator-enabled Lake, a compatible `lean4export` and bubblewrap available, run from this directory.

```sh
export LEAN_NUM_THREADS=1
lake comparator --config comparator.json
```

The expected result is exit status 0 and these final success lines.

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The retained run covers all fourteen declarations in one invocation. Its [standard output](evidence/ComparatorBoth.stdout.log), [standard error](evidence/ComparatorBoth.stderr.log) and [exit receipt](evidence/ComparatorBoth.receipt.json) are included. The comparator rejects the solution when `Classical.choice` is not permitted ("Illegal axiom detected") and against a challenge whose `replacement_fidelity` states the value 1/3 instead of 1/4 ("statement do not match"); see the `Negative-*` files.

## Other evidence

The [axiom audit](evidence/AuditBoth.log) records the axioms of 141 declarations: the supporting declarations of Lemma 6.6 and Theorem 8.2 and every declaration added in version 3.1.0. Each uses only `propext`, `Classical.choice` and `Quot.sound`. The proof closures rooted at `QuantumScope.bell_sharing_bound` and at `CertificationScope.abstract_window_certification`, and the closure of all 67 declarations added in version 3.1.0 together with those two, were also accepted by `leanchecker` and `nanoda`. The negative configurations remove `Classical.choice` from the allowed axioms and are rejected. The evidence filenames use `C01` for Lemma 6.6, `C02` for Theorem 8.2 and `C03` for the closure of the version 3.1.0 declarations ([roots](evidence/C03-roots.txt)). The [export digests](evidence/EXPORT-DIGESTS.txt) identify the closures used for those checks. [File manifest and hashes](MANIFEST.md)
