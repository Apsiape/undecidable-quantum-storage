# Undecidable quantum storage with seven elementary gates

Seth Douglas and Nidhal Mghirbi. Version 1.0.0, November 2026.

**This is a preprint. It has not been peer reviewed. The authors have not independently verified the mathematical arguments; see "How it was checked" below.**

## Abstract

Can the noise rate of one fixed local circuit encode an undecidable quantum-storage problem? Yes: we construct a three-dimensional medium, using only X, H, CNOT, Toffoli, reset, dephasing and identity, whose storage behaviour on explicit rate windows is as hard to decide as the halting problem. A separate construction handles each of whole-site and independent single-qubit depolarization after every layer. Computable disjoint rational rate windows select universal-machine inputs. For each nonhalting input, one computable encoder stores a reference-entangled qubit for a fixed positive multiple of the side length, at every size above a computable input-dependent threshold. On halting windows, every encoding fails after a time uniform in size and rate. A linear whole-channel upper bound makes the nonhalting storage scale sharp; certification of the explicit circuits is Π⁰₁-complete, with exact rational finite tests. The proof combines a noisy classical hierarchical calendar with concatenated binary quantum codes and a two-copy channel extension. A separate four-dimensional medium, under single-qubit depolarization only, has both an uncomputable storage diagram and a designed, decidable window of exponential storage. Interactions are finite-range rather than nearest-neighbour, constants are astronomical, and every finite sample eventually forgets.

## What the paper proves

Statement letters refer to `paper/main.pdf`; the statements are quoted from the paper with its notation written out in plain text. U is a fixed universal machine.

- **Theorem A.** "For each of whole-site and independent single-qubit depolarization after every layer, there is a separately constructed, computably specified, translation-invariant, time-periodic finite-range circuit on Z^3, with gate inventory {X, H, CNOT, Toffoli, R0, DZ, I} and computable disjoint rational windows I_n: nonhalting gives optimal storage time Θ(L); halting gives a time bound uniform in L and the window; certification of its explicit linear-time storage circuits is Π⁰₁-complete." In detail (Theorem 2.1): if U(n) never halts, then for every side L ≥ L0(n), with L0 computable, the explicit construction keeps entanglement fidelity at least 15/16 with a reference through time ⌊cL⌋, with c > 0 independent of n; if U(n) halts, every encoder and decoder into the whole medium has fidelity at most 1/2 + η after a time uniform in the volume and the window, for every η > 0; and on every window the whole channel is close to entanglement-breaking by time 201L + C0 (a time that depends on L).
- **Proposition C.1 (coexistence).** One computably specified, translation-invariant, finite-range, time-periodic circuit on Z^4, with the same seven gate types, under single-qubit depolarization only, has computable disjoint rational windows I_0, I_1, ...: on I_0, a designed and decidable window, it keeps fidelity at least 15/16 for all times up to 2^⌊cL⌋; on I_(n+1) it behaves as in Theorem A. Exponential storage on an undecidable window is not proved and remains open.

Scope, as the paper states it: the media are finite-range, not nearest-neighbour; the two noise models are handled by separate media; constants, local dimension and range are astronomical; encoding and final decoding are global computable maps, while the repeated correction inside the medium is local; nothing is classified outside the selected windows; every finite system eventually forgets, and the theorem concerns how useful storage time scales with size. Two dimensions and exponential storage on the undecidable windows remain open. Section 1 of the paper gives the full credits, including the fixed-rule two-dimensional quantum memories of Dünnweber, Styliaris and Trivedi, which already combine Gács-style hierarchical classical control with a measurement-free concatenated quantum code; the undecidable window structure, the destruction of every encoding, the sharp linear scale and the certification result are what this paper adds.

## Contents and reproduction

- `paper/main.pdf`: the manuscript (46 pages).
- `paper/`: the LaTeX source (`main.tex`, `sections/`, `references.tex`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times, and rejects warnings, unresolved references and box defects.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The paper's section "How this work was done" gives the account. The authors directed the work. GPT-6.1 Sol agents in Codesk sessions found the constructions and proofs, checked them in session, and drafted the text. Claude Opus 5.5 checked the results as a different model family, ran a literature check and reviewed the text; for the three-dimensional theorem there were two such checks, the second of which derived the fault-tolerance contract (Lemma 5.2 of the paper) independently, so that lemma is proved in the paper rather than cited. A final readback checked every revision against the proofs and reviews and rebuilt the paper. The authors have not independently verified the mathematical arguments. These are written proofs and model checks; there is no machine verification.

## Citation and rights

See `CITATION.cff` for citation metadata. Paper and documentation: CC BY 4.0. Script (`paper/build.py`): MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
