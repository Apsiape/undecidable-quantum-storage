# Lean proofs for Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers

These proofs accompany *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*, version 3.0.0.

| Paper result | Lean declaration |
|---|---|
| Lemma 6.6, the Bell-sharing bound | `QuantumScope.bell_sharing_bound` |
| Theorem 8.2, conditional window certification, the abstract form of Theorem 8.3 | `CertificationScope.abstract_window_certification` |

The Bell-sharing proof applies to every positive output count, finite-dimensional CPTP encoder and common decoder. The certification theorem takes the physical storage and forgetting bounds as hypotheses. [Formalization scope](SCOPE.md) · [Theorem 8.2 in LaTeX](docs/PRINTED-STATEMENT.tex)

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
```

Append these lines to separate copies of `Challenge.lean` and `Solution.lean` in this directory.

```lean
#check @QuantumScope.bell_sharing_bound
#check @CertificationScope.abstract_window_certification
```

Run `lake env lean -j1 -M5000` with each copy’s filename and compare the printed declaration types with `Challenge.lean` and the paper. The two `sorry` bodies in the frozen challenge expose the statements. The verified proofs are imported by `Solution.lean`.

## Comparator

The [Lean comparator](https://github.com/leanprover/comparator) mechanically compares both proved statements and their definitions against the frozen, Mathlib-only `Challenge.lean`. With a comparator-enabled Lake, a compatible `lean4export` and bubblewrap available, run from this directory.

```sh
export LEAN_NUM_THREADS=1
lake comparator --config comparator.json
```

The expected result is exit status 0 and these final success lines.

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The retained run covers both declarations in one invocation. Its [standard output](evidence/ComparatorBoth.stdout.log), [standard error](evidence/ComparatorBoth.stderr.log) and [exit receipt](evidence/ComparatorBoth.receipt.json) are included.

## Other evidence

The [axiom audit](evidence/AuditBoth.log) records the axioms of the supporting declarations. The proof closures rooted at the two declarations were also accepted by `leanchecker` and `nanoda`. The negative configurations remove `Classical.choice` from the allowed axioms and are rejected. The evidence filenames use `C01` for Lemma 6.6 and `C02` for Theorem 8.2. The [export digests](evidence/EXPORT-DIGESTS.txt) identify the closures used for those checks. [File manifest and hashes](MANIFEST.md)
