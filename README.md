# Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers

Seth Douglas and Nidhal Mghirbi. Preprint, version 3.1.0, November 2026. [Archive DOI](https://doi.org/10.5281/zenodo.24254845) (all versions)

## Abstract

Below a threshold noise rate, error correction lets larger quantum memories store a qubit for longer, without limit. Can the noise rate alone tell us whether a given noisy circuit does this? We construct fixed local circuits for which no algorithm can, already in one dimension under single-qubit noise. Each circuit is translation-invariant and time-periodic, with depolarizing noise on every wire after every layer, including all classical control. A computable list of disjoint rate intervals is indexed by the inputs n of a universal Turing machine; local noise statistics select the input that the circuit simulates, and halting triggers erasure. If the machine runs forever on n, a qubit is stored throughout the n-th interval at entanglement fidelity at least 15/16 for a time that grows without bound with size: linearly on rings, exponentially in six dimensions. The encoding and decoding maps are noiseless and global; they depend on n, the system size and, for decoding, the time, but not on the rate. If it halts, the fidelity of every encoding falls below 1/2+η, for any fixed η>0, after a time independent of size and rate. The labels of the intervals with unbounded storage form a Π⁰₁-complete set, and intervals of both kinds accumulate at zero, so these circuits have no noise threshold. Without rate selection, the ring construction is a translation-invariant, time-periodic memory: from an initialized classical hierarchy it stores a qubit for a time linear in the ring length at every sufficiently small rate, addressing the memory part of a one-dimensional question raised by Dünnweber, Styliaris and Trivedi. These are existence results: registers and interaction ranges are very large and the rates astronomically small.

## Results

- **Theorem A (six dimensions).** For both noise models, the fidelity guarantee on nonhalting windows lasts through 2^⌊cₑL⌋ rounds above a computable size threshold. Proposition 9.9 gives a coarse exp(Oₙ(L⁴)) lifetime upper bound in rounds and Π⁰₁-complete certification of the specified exponential-horizon storage circuits.
- **Theorem B (four dimensions).** Under whole-site depolarization, the guarantee lasts through ⌊exp(c₄L^α₄)⌋ elementary layers, including times between round boundaries. A full-register reset gives an exp(Oₙ(L⁴)) lifetime upper bound in elementary layers.
- **Theorem C (three dimensions).** For both noise models, the optimal lifetime at fidelity 7/8 on nonhalting windows is at least ⌊cL⌋ and less than 201L + C₀ rounds above a computable size threshold. Theorem 8.3 gives exact, Π⁰₁-complete certification for the linear-horizon construction.
- **Theorem D (one dimension).** On rings of L sites, under independent single-qubit depolarization after every elementary layer, one translation-invariant, time-periodic circuit has the same undecidable dichotomy: on nonhalting windows the fidelity guarantee lasts at least ⌊c₁L⌋ elementary layers above a computable size threshold; on halting windows every encoding forgets after a time independent of size and rate. The labels of scalable windows form a Π⁰₁-complete set.
- **Corollary 1.1 (a one-dimensional memory).** Without rate selection, the same construction is a translation-invariant, time-periodic memory on rings in which every wire, including all classical control, is noisy: from an initialized classical hierarchy it keeps Bell fidelity at least 15/16 for at least ⌊c_m L⌋ elementary layers, for all sufficiently large L, at every rate up to a fixed rational threshold. Dünnweber, Styliaris and Trivedi raised the one-dimensional case as open.
- **Corollaries 1.2 and 1.3.** Both kinds of window accumulate at zero, ruling out a positive noise threshold. For each circuit, the labels with unbounded optimal lifetime at every rate in the window form a Π⁰₁-complete set. The corresponding decision problem on rational rates in the windows is undecidable.
- **Appendix E.** A separate four-dimensional circuit under single-qubit depolarization has a reserved exponential-storage window and a tail family on which linear storage versus forgetting is undecidable.

On halting windows the forgetting time is uniform in lattice size and rate for any chosen fidelity tolerance above 1/2. Appendix J describes two Lean developments. `lean/` formalizes Lemmas 6.5 and 6.6, conditional forms of the full-replacement bound (2.3) and the associated lifetime estimates, a conditional abstract form of Theorem 6.7, the overlap step in the proof of Lemma 16.1, and Theorem 8.2, the conditional abstract form of Theorem 8.3. `lean-1d/` formalizes Lemmas 12.1 and 12.2, the arithmetic of Lemma 16.1 with its fidelity inputs supplied as hypotheses, and selected exponent calculations from Lemmas 14.1 and 14.2. Theorems A, B, C and D are not formalized.

## Archive contents

- `paper/` contains the manuscript PDF, the LaTeX source, figures, references and the abstract.
- `lean/` contains the Lean 4 library, its 14 frozen statements in `Challenge.lean`, the proof imports and axiom checks in `Solution.lean`, and the verification evidence.
- `lean-1d/` contains the second Lean development, for the one-dimensional construction and its classical inputs: its frozen statement file with 54 statements, the proofs, build and check scripts, and the comparator and kernel-replay evidence.
- `SHA256SUMS` lists the SHA-256 digest of each distributed file except the checksum list itself. Verify it from the archive root with `sha256sum -c SHA256SUMS`.

## Build the paper

From `paper/`, run the three pdfLaTeX passes described in Appendix H.

```sh
pdflatex main.tex
pdflatex main.tex
pdflatex main.tex
```

Appendix H gives the entry points for reconstructing the circuits, rate windows, encoders, decoders and exact fidelity queries. The tested engine is MiKTeX-pdfTeX 4.23 (MiKTeX 25.12).

## Build and check the Lean library

Use Lean 4.35.0 and Mathlib at commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. From `lean/` in a POSIX shell, run the Appendix J commands. The cache download is optional.

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M5000 Solution.lean
```

Each of the fourteen declarations should report exactly `propext`, `Classical.choice` and `Quot.sound`. To compare their printed types, append the following lines to separate copies of `Challenge.lean` and `Solution.lean` in `lean/`.

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

Run `lake env lean -j1 -M5000` with each copy’s filename and compare the printed types with `Challenge.lean` and the paper. The Lean comparator accepts all 14 frozen statements, and the axiom audit of 141 declarations finds only these three axioms. [Lean documentation and comparator evidence](lean/README.md)

### The one-dimensional development

From `lean-1d/`, with the same toolchain and Mathlib commit, run `lake exe cache get`, `lake build` and `lake comparator --config comparator.json`, or `scripts/check.sh` for the full chain (comparator, axiom audit and two independent kernel replays). The comparator and two independent kernel checkers accept all 54 frozen statements, and the 79 audited declarations use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. [Scope, statement-by-statement comparison and evidence](lean-1d/README.md)

## Changes in version 3.1.0

- The presentation was revised for the arXiv edition after version 3.0.0, with the mathematics unchanged: Section 1.3 adds an overview of the ring construction with Figure 4, Table 9 gives the terminology used on rings, Sections 12, 13, 14, 16 and 17 add proof-idea paragraphs, and the new Section 20 describes how the work was done.
- Lean coverage is added (Appendix J). `lean/` now also formalizes Lemma 6.5, conditional forms of the full-replacement bound (2.3) and the associated lifetime estimates, a conditional abstract form of Theorem 6.7 and the overlap step in the proof of Lemma 16.1; the comparator accepts its 14 frozen statements, and the axiom audit covers 141 declarations. `lean-1d/` now also formalizes Lemma 12.2, the arithmetic of Lemma 16.1 with its fidelity inputs supplied as hypotheses, and selected exponent calculations from Lemmas 14.1 and 14.2; the comparator and two independent kernel checkers accept its 54 frozen statements, and the axiom audit covers 79 declarations.
- Missing hypotheses, sizes and quantifier orders are now stated, one off-by-one in Proposition G.2 is corrected, and local names are made consistent.
- Theorems A, B, C and D retain their storage and forgetting guarantees.
- Version 3.0.0 is [10.5281/zenodo.24354983](https://doi.org/10.5281/zenodo.24354983).

## Changes in version 3.0.0

- Theorem D proves the undecidable storage dichotomy on rings under independent single-qubit depolarization after every elementary layer (Sections 11 to 18), building on the one-dimensional classical construction of the noise diagram, version 2.0.0 (10.5281/zenodo.24352353).
- Corollary 1.1 is the one-dimensional memory with every wire noisy. The earlier Corollaries 1.1 and 1.2 are now Corollaries 1.2 and 1.3, unchanged in statement.
- The abstract, introduction, discussion and Table 1 cover the one-dimensional results; the introduction credits the one-dimensional fault-tolerance literature.
- A second Lean development, `lean-1d/`, formalizes Lemma 12.1 with its classical inputs; the comparator and two independent kernel checkers accept its 43 theorems (Appendix J).
- Theorems A, B and C and every other statement of version 2.2.0 are unchanged; version 2.2.0 is [10.5281/zenodo.24350319](https://doi.org/10.5281/zenodo.24350319).

## Citation and license

Douglas, Seth, and Nidhal Mghirbi (2026). *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*. Version 3.1.0. [Archive DOI](https://doi.org/10.5281/zenodo.24254845) · [Citation metadata](CITATION.cff)

Paper and documentation are licensed under CC BY 4.0. The Lean sources are available under the MIT License or Apache License 2.0, at your option. [Licensing details](RIGHTS.md)
