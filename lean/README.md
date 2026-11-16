# Lean proofs accompanying the paper

This directory is the release repository's `lean/` folder for *Undecidable
quantum storage with seven elementary gates*, version 2.1.0.

The two completed targets are:

- C01, `QuantumScope.bell_sharing_bound`: Lemma 6.6 exactly as printed, for
  every positive output count k, every finite-dimensional CPTP encoder and
  common decoder, with the bound 1/2 + 1/(2k).
- C02, `CertificationScope.abstract_window_certification`: Theorem G.1,
  the printed conditional abstract form of Theorem 8.2. It proves equality
  with nonhalting, Pi01-completeness, rational/real equivalence and
  noncomputability, assuming the stated storage and forgetting premises.
  `docs/PRINTED-STATEMENT.tex` is the unchanged frozen statement and proof;
  the paper adjusts only its label and cross-reference syntax.

C01 uses transparent finite complex matrix definitions: positivity after
every finite ancillary amplification, trace preservation, partial-trace
marginals, the normalized Bell projector and its actual reference overlap.
Its operator bound and the common decoder's tensor-power extension are
proved. C02's physical inputs are hypotheses, not foundational axioms.

Theorems A, B and D, the concrete unconditional Theorem 8.2, every physical
premise of C02, all constructions (including encoders, decoders, circuits,
the extension for the medium and the exact polynomials), noise analysis
and seven-gate compilation are outside these proofs. See `SCOPE.md`.

## Pins and ordinary reproduction

- Lean `leanprover/lean4:v4.35.0`, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- `lake-manifest.json` pins all nine dependencies.

With the pinned toolchain installed, run from this directory in a POSIX
shell (the first line limits threads):

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M5000 Solution.lean
lake env lean -j1 -M5000 evidence/AuditBoth.lean
```

The default `QuantumStorage` library contains both proofs and has no proof
holes or new axiom declarations. `Solution.lean` imports it and prints the
two target axiom sets. `Challenge.lean` imports only Mathlib and has two
intentional `sorry` bodies for statement comparison; it is a nondefault
target and is not imported by the proved library. Its warnings are expected.
The retained build also has advisory module-system, unused-simp-argument
and unused-variable warnings; these are distinct from proof holes.

## Dated verification results

All final gates passed on **16 November 2026**. These are retained results
from the frozen proof package, not claims that this paper assembly reran Lean.

| Check | C01 | C02 | Evidence |
|---|---|---|---|
| Frozen statements read blind against the paper before any proof | PASS | PASS | FIDELITY summary below; unchanged statement/source hashes in MANIFEST |
| Complete proof and axiom audit | PASS | PASS | `evidence/AuditBoth.log`; 74 declarations use only `propext`, `Classical.choice`, `Quot.sound` |
| Sandboxed Mathlib-only Challenge/Solution comparison | PASS | PASS | `evidence/ComparatorBoth.stdout.log` and receipt: joint exit 0, 110 s |
| leanchecker replay | exit 0, 124 s | exit 0, 32 s | Per-target logs and receipts |
| nanoda replay | exit 0, 16 s | exit 0, 3 s | Per-target logs and receipts; successful runs have empty logs |
| Missing-Classical.choice control | expected exit 1 | expected exit 1 | Per-target negative logs and receipts |
| Static source lint | PASS | PASS | `evidence/LintBoth.log` and `source-audit-both.log` |
| Fresh clone, stock cache retrieval | exit 0, 83 s | same package | `evidence/CacheFresh.stdout.log` and receipt |
| Fresh clone, plain default build | exit 0, 47 s | same package | `evidence/BuildFresh.stdout.log` and receipt |

The blind statement read found no mismatch for either target, including
complete positivity in every finite ancillary dimension, full marginal
equality, all positive k, and each clause of C02. It preceded all proof
work. The frozen statement hash is
`f0b2cf6188616be5909635bb1b700649c9d171d026dee44e80bf7e66851a3db5`.
The fresh clone began without a `.lake` directory; cache retrieval
decompressed 9031 files, and the plain build completed 2833 scheduled or
cached jobs. All 24 then-delivered package files matched before and after;
the worktree stayed clean and actual Mathlib revision matched the pin.
`evidence/FRESH-CLONE-VERIFICATION.txt` retains source hashes.

## Comparator and independent kernels

The comparator requires a comparator-enabled Lake and bubblewrap.
With those additional tools available, run:

```sh
lake comparator --config comparator.json
```

The retained run used a real sandbox, fresh builds and exports, both
configured target names, and no supplied exports. It accepted both solution
types against the Mathlib-only frozen challenge and reported
"Lean default kernel accepts the solution" and "Your solution is okay!".
The comparator is an additional tool; it is not provided by stock Lake.

The independent checks used complete proof closures exported from
`Solution`, rooted respectively at the two fully qualified target names.
`leanchecker` accepted each closure; `nanoda` accepted each with the three
permitted axioms. Each negative configuration removes `Classical.choice`
from the permitted set and rejects the unchanged closure.
The relative-path nanoda configurations and both outputs/exit receipts
are in `evidence/`. Place newly generated complete exports at
`evidence/C01.ndjson` and `evidence/C02.ndjson`. Use a compatible nanoda's
configuration-file invocation with `nanoda-c01.json` and `nanoda-c02.json`,
then with the two `-negative.json` configurations. The negative runs must
reject the unpermitted axiom. Export generation and leanchecker replay
require the comparator/exporter tools in addition
to the pinned ordinary Lean package; they are not stock-build commands.
This compact release ships source and text receipts, rather than those
tools or compressed proof exports. To reproduce their independent replay,
regenerate both complete root closures with a compatible exporter and use
the checkers' supported export-input commands. The original plain-export
hashes and sizes are retained in `evidence/EXPORT-DIGESTS.txt`.

`MANIFEST.md` lists the SHA-256 of every payload file and its source,
relative to the frozen package root. Text transformations are identified.
`PATH-SCAN.txt` records the final scan for local paths and private workspace
names. No caches or compiled artifacts are included.
