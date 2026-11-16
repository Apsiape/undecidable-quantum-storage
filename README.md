# Undecidable quantum storage with seven elementary gates

Seth Douglas and Nidhal Mghirbi. Version 2.0.0, November 2026. DOI for all versions: [10.5281/zenodo.24254845](https://doi.org/10.5281/zenodo.24254845); version 2.0.0: [10.5281/zenodo.24269020](https://doi.org/10.5281/zenodo.24269020); version 1.0.0: [10.5281/zenodo.24254846](https://doi.org/10.5281/zenodo.24254846).

**This is a preprint. It has not been peer reviewed. The authors have not independently verified the mathematical arguments; see "How it was checked" below.**

## Abstract

Can one decide from its noise rate whether a fixed local quantum medium is an excellent memory or no scalable memory at all? We construct two six-dimensional media, one for whole-site and one for independent single-qubit depolarization, for which this distinction is undecidable. Both circuits use only X, H, CNOT, Toffoli, reset, dephasing and identity, with noise after every elementary layer. Computable disjoint rational windows select universal-machine inputs. For every nonhalting input and all sizes above a computable threshold, one total computable encoder preserves a reference-entangled qubit with fidelity at least 15/16 through an exponential number of rounds, uniformly across its window. On halting windows every encoding into the entire physical algebra fails after a time uniform in size and rate. A capped static computational chart and a protected finite counter permit exponential operation; complete source witnesses control correlated controller errors on the torus. For these media we give a coarse lifetime upper bound exponential in the fourth power of size and Π⁰₁-complete certification by exact finite tests. The three-dimensional construction retains its sharp linear storage scale. The interactions have fixed finite range and astronomical constants. Every finite sample eventually forgets; what is undecidable is how its useful storage time grows with size.

## What the paper proves

Statement letters refer to `paper/main.pdf`; the statements are quoted from the paper with its notation written out in plain text. U is a fixed universal machine.

- **Theorem B (new in version 2.0.0).** "For each of whole-site and independent single-qubit depolarization after every elementary layer, a separately compiled, computably specified, translation-invariant, time-periodic finite-range circuit on Z^6 with the same seven gates has computable disjoint rational windows I_n. For one rational c_e > 0, independent of n and the same for both media: if U(n) does not halt, one encoder keeps entanglement fidelity at least 15/16 at every rate in I_n and every time t ≤ 2^⌊c_e L⌋, for all L above a computable threshold L_e(n); if U(n) halts, every encoding is destroyed after a time uniform in L and the window." The encoder and the time-dependent decoder are total computable and do not depend on the rate or the halting answer (detailed form: Theorem 9.1).
- **Proposition 9.8 (new).** For both Z^6 media: on every window, the whole channel is close to entanglement-breaking by a time exp(O_n(L^4)), for every encoder and decoder (a coarse upper bound; below 2^(L^5) above a computable size cutoff); certification of the explicit exponential-horizon storage circuits is Π⁰₁-complete, with exact rational finite tests; and no total computable function of n bounds the size-independent forgetting time over halting inputs.
- **Theorem A (unchanged from version 1.0.0).** "For each of whole-site and independent single-qubit depolarization after every layer, there is a separately constructed, computably specified, translation-invariant, time-periodic finite-range circuit on Z^3, with gate inventory {X, H, CNOT, Toffoli, R0, DZ, I} and computable disjoint rational windows I_n: nonhalting gives optimal storage time Θ(L); halting gives a time bound uniform in L and the window; certification of its explicit linear-time storage circuits is Π⁰₁-complete."
- **Proposition C.1 (unchanged).** A four-dimensional medium, under single-qubit noise only, with a designed and decidable window of exponential storage beside the undecidable windows. Its dimension-four conclusion stands on its own; the open problem it pointed to, exponential storage on the undecidable windows, is answered by Theorem B.

Scope, as the paper states it: the interactions have fixed finite range, not nearest-neighbour; the two noise models are handled by separate media; constants, local dimension and range are astronomical; encoding and final decoding are global computable maps, while the repeated correction inside the medium is local; nothing is classified outside the selected windows; every finite system eventually forgets, and the theorems concern how useful storage time grows with size. Open: exponential storage below dimension six, two dimensions, and a matching exp(O(L)) lifetime upper bound for the exponential media. Sections 1 and 10 of the paper give the full credits, including the fixed-rule memories of Dünnweber, Styliaris and Trivedi and of Balasubramanian, Davydova and Lake, the fault-tolerant gadgets of Aharonov and Ben-Or, and the undecidability results of Cubitt, Pérez-García and Wolf and of Bausch, Cubitt and Watson. Where Section 9 reuses methods already published in version 1.0.0 or in the authors' noise-diagram and forgetting papers, it cites them at the point of use.

## Changes in 2.0.0

- New Theorem B and Section 9 (six new section files): exponential storage on the undecidable windows in Z^6, for both noise models, with the same seven gates; and Proposition 9.8 (a coarse exp(O_n(L^4)) upper bound, Π⁰₁-complete certification, no computable forgetting-time bound). The open problem of version 1.0.0 is answered.
- The abstract, introduction, figure, landscape table, discussion and open problems are updated; the account of how the work was done is one combination statement.
- Sections 2-8 and Appendices A-C are unchanged from version 1.0.0, byte for byte.

## Contents and reproduction

- `paper/main.pdf`: the manuscript (65 pages).
- `paper/`: the LaTeX source (`main.tex`, `sections/`, `references.tex`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times, and rejects warnings, unresolved references and box defects.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The paper's section "How this work was done" gives the account. The work used a combination of AI models (including Claude Opus 5.5, GPT-6.1 Sol and GPT-6 Astra), directed by the authors. Each new result was checked refutation-first by a model of a different developer from the one that found it, each check re-deriving the steps new at that stage; the checks also used small exact computations and simulations. The written version was reviewed the same way and had a final readback. The authors have not independently verified the mathematical arguments. These are written proofs and model checks; there is no machine verification yet.

## Citation and rights

See `CITATION.cff` for citation metadata. Paper and documentation: CC BY 4.0. Script (`paper/build.py`): MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
