# Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers

Seth Douglas and Nidhal Mghirbi. Preprint, version 3.0.0, November 2026. [Archive DOI](https://doi.org/10.5281/zenodo.24254845) (all versions)

## Abstract

A quantum memory is usually judged by its threshold: below some noise rate, larger memories store quantum information for longer, without limit. We construct fixed local noisy quantum circuits for which no algorithm can decide, from the noise rate, whether this happens, already in one dimension. Each circuit is translation-invariant, time-periodic and finite-range, with depolarizing noise after every layer, including on all classical control. A computable list of disjoint intervals of noise rates is indexed by the inputs n of a universal Turing machine. If the machine runs forever on n, then at every rate in the n-th interval rate-independent encoding and decoding maps keep a qubit, entangled with a reference, at fidelity at least 15/16 for a time growing without limit with system size. If it halts, every encoding loses this fidelity after a time independent of size and rate. The labels of scalable intervals form a Π⁰₁-complete set, and intervals of both kinds accumulate at zero, so the circuits have no noise threshold. Storage lower bounds are linear in L on rings of L sites under single-qubit noise, exponential in side length in six dimensions under single-qubit or whole-site noise, stretched-exponential in four under whole-site noise, and linear in three under either model. The rate is never an input: local noise samples select a computation whose halting triggers erasure, and a no-cloning bound controls every encoding. Without rate selection, the one-dimensional construction is a translation-invariant, time-periodic quantum memory with every wire, including all control, noisy; initialized with a classical hierarchy, it stores a qubit for at least cL layers, with fixed c > 0, at every small enough rate, a case raised as open by Dünnweber, Styliaris and Trivedi. These are existence results: registers and ranges are very large, rates astronomically small.

## Results

- **Theorem A (six dimensions).** For both noise models, the fidelity guarantee on nonhalting windows lasts through 2^⌊cₑL⌋ rounds above a computable size threshold. Proposition 9.9 gives a coarse exp(Oₙ(L⁴)) lifetime upper bound in rounds and Π⁰₁-complete certification of the specified exponential-horizon storage circuits.
- **Theorem B (four dimensions).** Under whole-site depolarization, the guarantee lasts through ⌊exp(c₄L^α₄)⌋ elementary layers, including times between round boundaries. A full-register reset gives an exp(Oₙ(L⁴)) lifetime upper bound in elementary layers.
- **Theorem C (three dimensions).** For both noise models, the optimal lifetime at fidelity 7/8 on nonhalting windows is at least ⌊cL⌋ and less than 201L + C₀ rounds above a computable size threshold. Theorem 8.3 gives exact, Π⁰₁-complete certification for the linear-horizon construction.
- **Theorem D (one dimension).** On rings of L sites, under independent single-qubit depolarization after every elementary layer, one translation-invariant, time-periodic circuit has the same undecidable dichotomy: on nonhalting windows the fidelity guarantee lasts at least ⌊c₁L⌋ elementary layers above a computable size threshold; on halting windows every encoding forgets after a time independent of size and rate. The labels of scalable windows form a Π⁰₁-complete set.
- **Corollary 1.1 (a one-dimensional memory).** Without rate selection, the same construction is a translation-invariant, time-periodic memory on rings in which every wire, including all classical control, is noisy: from an initialized classical hierarchy it keeps Bell fidelity at least 15/16 for at least ⌊c_m L⌋ elementary layers, for all sufficiently large L, at every rate up to a fixed rational threshold. Dünnweber, Styliaris and Trivedi raised the one-dimensional case as open.
- **Corollaries 1.2 and 1.3.** Both kinds of window accumulate at zero, ruling out a positive noise threshold. For each circuit, the labels with unbounded optimal lifetime at every rate in the window form a Π⁰₁-complete set. The corresponding decision problem on rational rates in the windows is undecidable.
- **Appendix E.** A separate four-dimensional circuit under single-qubit depolarization has a reserved exponential-storage window and a tail family on which linear storage versus forgetting is undecidable.

On halting windows the forgetting time is uniform in lattice size and rate for any chosen fidelity tolerance above 1/2. Lemma 6.6 and Theorem 8.2, the conditional abstract form of Theorem 8.3, are the two Lean results described in Appendix J.

## Archive contents

- `paper/` contains the manuscript PDF, the LaTeX source, figures, references and the abstract.
- `lean/` contains the Lean 4 library, the frozen statements in `Challenge.lean`, the proof imports and axiom checks in `Solution.lean`, and the verification evidence.
- `lean-1d/` contains the second Lean development: Lemma 12.1, the probability estimate of the one-dimensional construction, with its classical inputs, its frozen statement file, build and check scripts, and the comparator and kernel-replay evidence.
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

Each of the two declarations should report exactly `propext`, `Classical.choice` and `Quot.sound`. To compare their printed types, append the following lines to separate copies of `Challenge.lean` and `Solution.lean` in `lean/`.

```lean
#check @QuantumScope.bell_sharing_bound
#check @CertificationScope.abstract_window_certification
```

Run `lake env lean -j1 -M5000` with each copy’s filename and compare the printed types with `Challenge.lean` and the paper. [Lean documentation and comparator evidence](lean/README.md)

### The one-dimensional development

From `lean-1d/`, with the same toolchain and Mathlib commit, run `lake exe cache get`, `lake build` and `lake comparator --config comparator.json`, or `scripts/check.sh` for the full chain (comparator, axiom audit and two independent kernel replays). All 43 theorems use only `propext`, `Classical.choice` and `Quot.sound`. [Scope, statement-by-statement comparison and evidence](lean-1d/README.md)

## Changes in version 3.0.0

- Theorem D proves the undecidable storage dichotomy on rings under independent single-qubit depolarization after every elementary layer (Sections 11 to 18), building on the one-dimensional classical construction of the noise diagram, version 2.0.0 (10.5281/zenodo.24352353).
- Corollary 1.1 is the one-dimensional memory with every wire noisy. The earlier Corollaries 1.1 and 1.2 are now Corollaries 1.2 and 1.3, unchanged in statement.
- The abstract, introduction, discussion and Table 1 cover the one-dimensional results; the introduction credits the one-dimensional fault-tolerance literature.
- A second Lean development, `lean-1d/`, formalizes Lemma 12.1 with its classical inputs; the comparator and two independent kernel checkers accept its 43 theorems (Appendix J).
- Theorems A, B and C and every other statement of version 2.2.0 are unchanged; version 2.2.0 is [10.5281/zenodo.24350319](https://doi.org/10.5281/zenodo.24350319).

## Citation and license

Douglas, Seth, and Nidhal Mghirbi (2026). *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*. Version 3.0.0. [Archive DOI](https://doi.org/10.5281/zenodo.24254845) · [Citation metadata](CITATION.cff)

Paper and documentation are licensed under CC BY 4.0. The Lean sources are available under the MIT License or Apache License 2.0, at your option. [Licensing details](RIGHTS.md)
