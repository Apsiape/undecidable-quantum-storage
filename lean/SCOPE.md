# Lean formalization scope

This library accompanies *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*, version 2.2.0.

| Paper result | Coverage |
|---|---|
| Lemma 6.6, Bell-sharing bound | `QuantumScope.bell_sharing_bound` proves the bound 1/2 + 1/(2k) for every positive k, finite-dimensional CPTP encoder and common decoder. |
| Theorem 8.2, conditional window certification | `CertificationScope.abstract_window_certification` proves the equivalence with nonhalting, Π⁰₁-completeness, rational/real equivalence and noncomputability under the explicit storage and forgetting hypotheses. |

The Bell-sharing result uses complex matrix channels, complete positivity after every finite ancillary amplification, trace preservation, equal partial-trace marginals on every input, and fidelity with the normalized Bell projector. The auxiliary decoder-extension theorem starts from a supplied equal-marginal extension.

The conditional certification proof uses an exact computable Boolean test and a computable compiler. It proves Π⁰₁ membership by enumerating the finite tests, hardness by a reduction from nonhalting, and rational/real equivalence by continuity and density.

Theorems A, B and C, construction of the physical channels and their extensions, the physical storage and forgetting hypotheses, the noise analysis, the gate compilation, the circuits and the concrete certification results of Theorem 8.3 and Proposition 9.9 are outside the formalization. [Appendix J in the paper](../paper/main.pdf)
