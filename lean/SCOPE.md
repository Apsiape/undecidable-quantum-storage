# Formalization scope

| Paper result / selected target | Lean coverage | Status |
|---|---|---|
| Lemma 6.6, full Bell-sharing bound, all positive k, arbitrary CPTP encoder/common decoder | `QuantumScope.bell_sharing_bound`; actual finite complex matrix channels, full marginal equality, normalized Bell reference | PROVED |
| Theorem G.1, conditional abstract form of Theorem 8.2, exactly docs/PRINTED-STATEMENT.tex | `CertificationScope.abstract_window_certification` | PROVED |
| Equality of rationally certified inputs with nonhalting | `certificate_iff_nonhalting` | PROVED under explicit storage/forgetting hypotheses |
| Computable exact tests imply Pi01 membership | `certificate_pi01` | PROVED |
| Universal nonhalting is Pi01-hard via a computable compiler | `nonhalting_hard` | PROVED, including the partial-recursive failed-test search |
| Rational/real polynomial certification equivalence | `rational_iff_real` | PROVED by continuity and rational density |
| Undecidability of the conditional certified predicate | Final conjunct of C02 | PROVED using Mathlib's halting theorem and the supplied compiler |
| Original concrete, unconditional Theorem 8.2 | The separately printed conditional abstraction above | NOT formalized |
| Seven-gate construction, controller, three-dimensional medium, encoder/decoder circuits, exact polynomial construction | Data and physical premises are explicit; their concrete realization is not proved | NOT formalized |
| Nonhalting 15/16 storage and halting 9/16 forgetting estimates for the paper's medium | Explicit StorageInput and ForgettingInput hypotheses of C02 | NOT proved for the concrete medium |
| Construction of an extension for the paper's physical channel, extension iteration, uniform quantum forgetting theorem, EB mixture, Theorems A/B/D | No formalization of those physical results | NOT formalized |

C01 uses the unchanged frozen definitions. Complete positivity quantifies over
all finite ancillary dimensions, extension equality ranges over every input
matrix, and fidelity is the actual normalized Bell-reference overlap. The
proof derives the needed operator inequality from finite matrices; it does
not introduce an abstract fidelity functional or an inequality hypothesis.
The auxiliary decoder-extension theorem constructs an extension after any
encoder/common decoder from a supplied CPTP equal-marginal extension. It does
not construct the paper's physical extension from its medium.

C02's data are precisely those in the proposed printed conditional theorem.
The exact computable Boolean test is the computational hypothesis; separate
computability of endpoints, polynomials or the rational surjection is not
assumed. The paper's physical estimates remain explicit premises and are not
promoted into axioms or a claim that the concrete medium was built in Lean.

For the current paper, Theorems A, B and D, every physical premise of C02,
all constructions, the noise analysis and the seven-gate compilation remain
outside Lean coverage. The concrete unconditional Theorem 8.2 is not C02;
the exact conditional statement is printed as Theorem G.1 in Appendix G.
