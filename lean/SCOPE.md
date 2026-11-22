# Lean formalization scope

This library accompanies *Undecidable quantum storage: no algorithm can tell from the noise rate whether a fixed circuit remembers*, version 3.1.0.

| Paper result | Coverage |
|---|---|
| Lemma 6.5, iteration of equal-marginal extensions | `QuantumScope.iteration_extension` proves that a two-output equal-marginal extension of T gives a 2^j-output one of T^j for every positive j. `QuantumScope.equalMarginalExtension_comp` proves the composition step for any output counts k and m. |
| Lemma 6.6, Bell-sharing bound | `QuantumScope.bell_sharing_bound` proves the bound 1/2 + 1/(2k) for every positive k, finite-dimensional CPTP encoder and common decoder. |
| Lemmas 6.5 and 6.6 together | `QuantumScope.iterated_cloning_bound` proves the bound 1/2 + 2^(-j-1) through T^j for every CPTP encoder and decoder. |
| Theorem 6.7, conditional abstract form | `QuantumScope.uniform_forgetting` proves one forgetting time C, uniform over all sizes and rates, after which every encoder and decoder has fidelity at most 1/2 + η, also after any later partial round. It assumes the two-output extension of Proposition 6.4 on the large systems and the full-replacement decomposition on the small ones. |
| Theorem 8.2, conditional window certification | `CertificationScope.abstract_window_certification` proves the equivalence with nonhalting, Π⁰₁-completeness, rational/real equivalence and noncomputability under the explicit storage and forgetting hypotheses. |
| Full-replacement bound (2.3), Sections 10 and 18 | `QuantumScope.replacement_fidelity` proves the value 1/4 after a full replacement. `QuantumScope.replacement_ceiling` (layer by layer) and `QuantumScope.replacement_ceiling_pow` (one round channel) prove 1/4 + (3/4)(1-p)^t when each layer replaces the whole register with weight at least p. `QuantumScope.replacement_lifetime_layer` and `QuantumScope.replacement_lifetime` give τ ≤ log(6/5)/p < 1/p. |
| Lemma 16.1, the overlap step of its proof | `QuantumScope.good_event_fidelity_union` proves that a mixture of channels that recovers the encoded qubit exactly outside two failure events has fidelity at least one minus their probabilities. |

Proposition 6.4, the circuits and the noise analysis remain outside the formalization; Theorem 6.7 is checked from the extension onward. The library also proves that every noisy layer of the WS and Q models, written as a tensor power of ε R_σ + (1-ε) id over the register's factors, replaces the whole register with weight ε^N (`QuantumScope.depolarizing_tensorPower`, `QuantumScope.noisy_circuit_ceiling`).

The Bell-sharing result uses complex matrix channels, complete positivity after every finite ancillary amplification, trace preservation, equal partial-trace marginals on every input, and fidelity with the normalized Bell projector. The auxiliary decoder-extension theorem starts from a supplied equal-marginal extension.

The conditional certification proof uses an exact computable Boolean test and a computable compiler. It proves Π⁰₁ membership by enumerating the finite tests, hardness by a reduction from nonhalting, and rational/real equivalence by continuity and density.

Theorems A, B, C and D, Proposition 6.4, construction of the physical channels, the physical storage and forgetting hypotheses, the noise analysis, the gate compilation, the circuits and the concrete certification results of Theorem 8.3 and Proposition 9.9 are outside the formalization. [Appendix J in the paper](../paper/main.pdf)
