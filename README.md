# Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers

Seth Douglas and Nidhal Mghirbi. Preprint, version 2.2.0, November 2026. [Archive DOI](https://doi.org/10.5281/zenodo.24254845) (all versions); version 2.2.0: [10.5281/zenodo.24350319](https://doi.org/10.5281/zenodo.24350319)

## Abstract

A quantum memory is usually judged by its threshold: below some noise rate, larger memories store quantum information for longer, without limit. We construct fixed local noisy quantum circuits for which no algorithm can decide, from a rational noise rate, whether the best achievable storage time grows without limit with system size. For each of two noise models, whole-site and single-qubit depolarization after every layer, the circuit is translation-invariant and time-periodic on six-dimensional tori of side L. A computable list of disjoint intervals of noise rates is indexed by the inputs n of a universal Turing machine. If the machine runs forever on n, then at every rate in the n-th interval a rate-independent encoding keeps a qubit, entangled with a reference, at fidelity at least 15/16 for at least exponentially many rounds in L, for all L above a computable size. If it halts, every encoding loses this fidelity after a number of rounds that depends on neither L nor the rate. No algorithm can decide which case holds, and intervals of both kinds accumulate at zero, so the circuits have no noise threshold. The rate is never an input: local noise samples select the computation, its halting triggers local erasure of the quantum data, and a no-cloning bound controls every encoding. Related circuits show the same dichotomy with storage time at least stretched-exponential in L in four dimensions under whole-site noise, and of order L in three dimensions under both noise models. These are existence results: registers and interaction ranges are very large and the noise rates astronomically small.

## Results

- **Theorem A (six dimensions).** For both noise models, the fidelity guarantee on nonhalting windows lasts through 2^⌊cₑL⌋ rounds above a computable size threshold. Proposition 9.9 gives a coarse exp(Oₙ(L⁴)) lifetime upper bound in rounds and Π⁰₁-complete certification of the specified exponential-horizon storage circuits.
- **Theorem B (four dimensions).** Under whole-site depolarization, the guarantee lasts through ⌊exp(c₄L^α₄)⌋ elementary layers, including times between round boundaries. A full-register reset gives an exp(Oₙ(L⁴)) lifetime upper bound in elementary layers.
- **Theorem C (three dimensions).** For both noise models, the optimal lifetime at fidelity 7/8 on nonhalting windows is at least ⌊cL⌋ and less than 201L + C₀ rounds above a computable size threshold. Theorem 8.3 gives exact, Π⁰₁-complete certification for the linear-horizon construction.
- **Corollaries 1.1 and 1.2.** Both kinds of window accumulate at zero, ruling out a positive noise threshold. For each circuit, the labels with unbounded optimal lifetime at every rate in the window form a Π⁰₁-complete set. The corresponding decision problem on rational rates in the windows is undecidable.
- **Appendix E.** A separate four-dimensional circuit under single-qubit depolarization has a reserved exponential-storage window and a tail family on which linear storage versus forgetting is undecidable.

On halting windows the forgetting time is uniform in lattice size and rate for any chosen fidelity tolerance above 1/2. Lemma 6.6 and Theorem 8.2, the conditional abstract form of Theorem 8.3, are the two Lean results described in Appendix J.

## Archive contents

- `paper/` contains the manuscript PDF, the LaTeX source, figures, references and the abstract.
- `lean/` contains the Lean 4 library, the frozen statements in `Challenge.lean`, the proof imports and axiom checks in `Solution.lean`, and the verification evidence.
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

## Changes in version 2.2.0

- Corollary 1.2 identifies the labels of windows with unbounded optimal lifetime as a Π⁰₁-complete set and proves undecidability for rational rates in the windows.
- Theorem A denotes the six-dimensional result, Theorem B the four-dimensional result, and Theorem C the three-dimensional result. Theorem 8.2 is the conditional certification theorem; Theorem 8.3 is its concrete linear-horizon application.
- Lemma 5.2 spells out deterministic verified preparation of the Toffoli resource state, including its fresh verified blocks, cats and fault accounting.
- Lifetime bounds specify rounds for Theorems A and C and elementary layers for Theorem B, including intermediate layers. Proposition 9.9 gives the six-dimensional fibre-reset upper bound; (10.2) gives the four-dimensional full-register reset bound.
- The title is *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*.
- Lemma A.3a bounds every intermediate syndrome in the full sweep round by a fixed neighbourhood of the initial syndrome and the round's insertion catalogue, for both CSS sectors and for each folded sheet.
- Lemma 5.3a proves that clean requests form matchings at every level, assigns each child location to exactly one parent table, and derives uniform support and incidence bounds with no tokens crossing a parent-period boundary.
- Proposition 3.6 closes the boundary field from the upper slab row, separates complete boundary and future physical source supports, and traces late liveness back through that strengthened field uniformly over initial words.
- Lemma 3.7 gives the rare-proposal alternatives from an arbitrary starting time, with complete two-time seed supports and the joint bound for seed groups using the eight-class overlap divisor.
- Proposition 7.1 specifies the scaffold projection from the compiled chart and proves that local chart completion preserves both shared scaffold edges.
- Lemma B.2 requires N₀ = ⌊(L − 1)/R_phys⌋ ≥ 36 and gives the raw-cutoff exponent N₀/(72c₀), accounting for the physical flags represented by distinct raw names.

## Citation and license

Douglas, Seth, and Nidhal Mghirbi (2026). *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*. Version 2.2.0. [Archive DOI](https://doi.org/10.5281/zenodo.24254845) · [Citation metadata](CITATION.cff)

Paper and documentation are licensed under CC BY 4.0. The Lean sources are available under the MIT License or Apache License 2.0, at your option. [Licensing details](RIGHTS.md)
