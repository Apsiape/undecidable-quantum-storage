import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- Frozen release challenge. The target proofs are intentionally omitted.
   Sprint 1 (21 Nov 2026) adds twelve statements after bell_sharing_bound. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace QuantumScope

abbrev Mat (α : Type) := Matrix α α ℂ
abbrev QMap (α β : Type) [Fintype α] [Fintype β] := Mat α →ₗ[ℂ] Mat β

noncomputable def amplify {α β : Type} [Fintype α] [Fintype β]
    (r : ℕ) (T : QMap α β) (ρ : Mat (Fin r × α)) : Mat (Fin r × β) :=
  fun u v => T (fun x y => ρ (u.1, x) (v.1, y)) u.2 v.2

-- Complete positivity is quantified over every finite ancillary dimension.
-- This transparent finite-matrix definition avoids an unproved CPTP black box.
def IsCPTP {α β : Type} [Fintype α] [Fintype β] (T : QMap α β) : Prop :=
  (∀ ρ, Matrix.trace (T ρ) = Matrix.trace ρ) ∧
  (∀ (r : ℕ) (ρ : Mat (Fin r × α)),
    ρ.PosSemidef → (amplify r T ρ).PosSemidef)

noncomputable def marginal {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) (ρ : Mat (Fin k → β)) : Mat β :=
  fun x y => ∑ v : Fin k → β,
    if v j = x then ρ v (Function.update v j y) else 0

def HasEqualMarginalExtension {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (k : ℕ) (T : QMap α β) : Prop :=
  ∃ S : QMap α (Fin k → β), IsCPTP S ∧
    ∀ (j : Fin k) (ρ : Mat α), marginal k j (S ρ) = T ρ

-- |beta><beta| for beta = (|00> + |11>)/sqrt(2).
noncomputable def bell : Mat (Fin 2 × Fin 2) :=
  fun u v => if u.1 = u.2 ∧ v.1 = v.2 then (1 / 2 : ℂ) else 0

noncomputable def entanglementFidelity {α β : Type}
    [Fintype α] [Fintype β] (E : QMap (Fin 2) α)
    (T : QMap α β) (D : QMap β (Fin 2)) : ℝ :=
  (Matrix.trace (bell * amplify 2 (D.comp (T.comp E)) bell)).re

/-- Paper v2, Lemma 6.6 (f:bell), with all channel semantics expanded above.
Every encoder and common decoder are quantified; k is positive. -/
theorem bell_sharing_bound
    (a b k : ℕ) (hk : 0 < k)
    (T : QMap (Fin a) (Fin b)) (hT : IsCPTP T)
    (hExt : HasEqualMarginalExtension k T)
    (E : QMap (Fin 2) (Fin a)) (hE : IsCPTP E)
    (D : QMap (Fin b) (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E T D ≤ (1 / 2 : ℝ) + 1 / (2 * (k : ℝ)) := by
  sorry

-- Lemma 6.5 (f:iteration), composition step of its proof: k- and m-output extensions compose to
-- k*m outputs.
theorem equalMarginalExtension_comp {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (k m : ℕ) (T : QMap α β) (U : QMap β γ)
    (hT : HasEqualMarginalExtension k T) (hU : HasEqualMarginalExtension m U) :
    HasEqualMarginalExtension (k * m) (U.comp T) := by
  sorry

-- Lemma 6.5 (f:iteration), as printed: T^j has a 2^j-output extension for every positive j.
theorem iteration_extension {α : Type} [Fintype α] [DecidableEq α]
    (T : QMap α α) (hExt : HasEqualMarginalExtension 2 T) (j : ℕ) (hj : 1 ≤ j) :
    HasEqualMarginalExtension (2 ^ j) (T ^ j) := by
  sorry

-- Lemmas 6.5 and 6.6 together (proof of Theorem 6.7): fidelity through T^j is at most 1/2 +
-- 2^(-j-1); hT is implied by hExt, kept to mirror "channel".
theorem iterated_cloning_bound (a : ℕ) (T : QMap (Fin a) (Fin a)) (hT : IsCPTP T)
    (hExt : HasEqualMarginalExtension 2 T) (j : ℕ) (hj : 1 ≤ j)
    (E : QMap (Fin 2) (Fin a)) (hE : IsCPTP E)
    (D : QMap (Fin a) (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (T ^ j) D ≤ (1 / 2 : ℝ) + 1 / 2 ^ (j + 1) := by
  sorry

-- Proof of Theorem 6.7 and Section 18: after a full replacement the fidelity is exactly 1/4;
-- later evolution is absorbed into D.
theorem replacement_fidelity {α β : Type} [Fintype α] [Fintype β]
    (X : QMap α β) (hX : IsCPTP X) (σ : Mat β) (hσ : Matrix.trace σ = 1)
    (R : QMap β β) (hR : ∀ ρ, R ρ = Matrix.trace ρ • σ)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap β (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (R.comp X) D = 1 / 4 := by
  sorry

-- Full-replacement ceiling 1/4 + (3/4)(1-p)^t, layer form (Sections 10 and 18, elementary
-- layers); Gamma t = Lambda_(t-1) o ... o Lambda_0; conditional abstract form: hΛ is whole-
-- register replacement with probability >= p in each layer, independently.
theorem replacement_ceiling {α : Type} [Fintype α] (p : ℝ) (t : ℕ)
    (Λ : ℕ → QMap α α) (q : ℕ → ℝ) (σ : ℕ → Mat α) (Φ : ℕ → QMap α α)
    (hq : ∀ i, p ≤ q i ∧ q i ≤ 1) (hσ : ∀ i, Matrix.trace (σ i) = 1)
    (hΦ : ∀ i, IsCPTP (Φ i))
    (hΛ : ∀ i ρ, Λ i ρ = (q i : ℂ) • (Matrix.trace ρ • σ i) + (1 - (q i : ℂ)) • Φ i ρ)
    (Γ : ℕ → QMap α α) (hΓ0 : Γ 0 = LinearMap.id)
    (hΓ : ∀ i, Γ (i + 1) = (Λ i).comp (Γ i))
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap α (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (Γ t) D ≤ 1 / 4 + 3 / 4 * (1 - p) ^ t := by
  sorry

-- Full-replacement ceiling, round form: equation (eq:finite-reset) and the proof of Theorem
-- 6.7; conditional abstract form (one decomposition q >= p of the round channel).
theorem replacement_ceiling_pow {α : Type} [Fintype α] (p q : ℝ) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (Λ : QMap α α) (σ : Mat α) (hσ : Matrix.trace σ = 1) (Φ : QMap α α) (hΦ : IsCPTP Φ)
    (hΛ : ∀ ρ, Λ ρ = (q : ℂ) • (Matrix.trace ρ • σ) + (1 - (q : ℂ)) • Φ ρ) (t : ℕ)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap α (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (Λ ^ t) D ≤ 1 / 4 + 3 / 4 * (1 - p) ^ t := by
  sorry

-- Lifetime arithmetic behind (f4:lifetime-upper) and Section 18: t <= log(6/5)/p < 1/p.
theorem replacement_lifetime (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (t : ℕ)
    (h : (7 / 8 : ℝ) ≤ 1 / 4 + 3 / 4 * (1 - p) ^ t) :
    (t : ℝ) ≤ Real.log (6 / 5) / p ∧ Real.log (6 / 5) / p < 1 / p := by
  sorry

-- Sections 10 and 18, tau bound: at every t > log(6/5)/p one constant c < 7/8 bounds every
-- encoder and decoder, so F*(t) < 7/8 and tau <= log(6/5)/p < 1/p (with replacement_lifetime).
theorem replacement_lifetime_layer {α : Type} [Fintype α] (p : ℝ) (hp : 0 < p) (t : ℕ)
    (Λ : ℕ → QMap α α) (q : ℕ → ℝ) (σ : ℕ → Mat α) (Φ : ℕ → QMap α α)
    (hq : ∀ i, p ≤ q i ∧ q i ≤ 1) (hσ : ∀ i, Matrix.trace (σ i) = 1)
    (hΦ : ∀ i, IsCPTP (Φ i))
    (hΛ : ∀ i ρ, Λ i ρ = (q i : ℂ) • (Matrix.trace ρ • σ i) + (1 - (q i : ℂ)) • Φ i ρ)
    (Γ : ℕ → QMap α α) (hΓ0 : Γ 0 = LinearMap.id)
    (hΓ : ∀ i, Γ (i + 1) = (Λ i).comp (Γ i))
    (ht : Real.log (6 / 5) / p < t) :
    ∃ c : ℝ, c < 7 / 8 ∧
      ∀ (E : QMap (Fin 2) α), IsCPTP E → ∀ (D : QMap α (Fin 2)), IsCPTP D →
        entanglementFidelity E (Γ t) D ≤ c := by
  sorry

-- The ceiling is at most 1/2 + eta after a finite time (choice of t_n in Theorem 6.7).
theorem replacement_eventually (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → 1 / 4 + 3 / 4 * (1 - p) ^ t ≤ 1 / 2 + η := by
  sorry

-- Theorem 6.7 (f:forgetting) with Remark 6.8, conditional abstract form: the extension of
-- Proposition 6.4 and the full-replacement decomposition are hypotheses. C counts rounds; layer
-- cutoff J*C via M = the first r layers.
theorem uniform_forgetting {Θ : Type} (dim : Θ → ℕ)
    (Λ : (θ : Θ) → QMap (Fin (dim θ)) (Fin (dim θ))) (hΛ : ∀ θ, IsCPTP (Λ θ))
    (Small : Set Θ) (s : ℕ)
    (hExt : ∀ θ, θ ∉ Small → HasEqualMarginalExtension 2 (Λ θ ^ s))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (q : Θ → ℝ) (σ : (θ : Θ) → Mat (Fin (dim θ)))
    (Φ : (θ : Θ) → QMap (Fin (dim θ)) (Fin (dim θ)))
    (hRep : ∀ θ, θ ∈ Small → p ≤ q θ ∧ q θ ≤ 1 ∧ Matrix.trace (σ θ) = 1 ∧
      IsCPTP (Φ θ) ∧
      ∀ ρ, Λ θ ρ = (q θ : ℂ) • (Matrix.trace ρ • σ θ) + (1 - (q θ : ℂ)) • Φ θ ρ)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℕ, ∀ (θ : Θ) (t : ℕ), C ≤ t →
      ∀ M : QMap (Fin (dim θ)) (Fin (dim θ)), IsCPTP M →
      ∀ E : QMap (Fin 2) (Fin (dim θ)), IsCPTP E →
      ∀ D : QMap (Fin (dim θ)) (Fin 2), IsCPTP D →
        entanglementFidelity E (M.comp (Λ θ ^ t)) D ≤ 1 / 2 + η := by
  sorry

-- Proof of Lemma 16.1 (q1:l18), helper: the overlap is at least the weight of the good
-- branches.
theorem good_event_fidelity {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ι → QMap α β) (hB : ∀ i, IsCPTP (B i))
    (T : QMap α β) (hT : T = ∑ i, (w i : ℂ) • B i) (G : Finset ι)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap β (Fin 2)) (hD : IsCPTP D)
    (hG : ∀ i ∈ G, D.comp ((B i).comp E) = LinearMap.id) :
    ∑ i ∈ G, w i ≤ entanglementFidelity E T D := by
  sorry

-- Proof of Lemma 16.1 (q1:l18), as printed: the overlap is at least one minus the two failure
-- probabilities.
theorem good_event_fidelity_union {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (B : ι → QMap α β) (hB : ∀ i, IsCPTP (B i))
    (T : QMap α β) (hT : T = ∑ i, (w i : ℂ) • B i) (G F₁ F₂ : Finset ι)
    (hcover : ∀ i, i ∉ G → i ∈ F₁ ∨ i ∈ F₂)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap β (Fin 2)) (hD : IsCPTP D)
    (hG : ∀ i ∈ G, D.comp ((B i).comp E) = LinearMap.id) :
    1 - ∑ i ∈ F₁, w i - ∑ i ∈ F₂, w i ≤ entanglementFidelity E T D := by
  sorry


end QuantumScope



set_option autoImplicit false

namespace CertificationScope

-- A semantic Pi^0_1 definition, including computability rather than mere decidability.
def IsPi01 (P : ℕ → Prop) : Prop :=
  ∃ R : ℕ × ℕ → Bool, Computable R ∧ ∀ n, P n ↔ ∀ s, R (n, s) = true

def IsPi01Complete (P : ℕ → Prop) : Prop :=
  IsPi01 P ∧ ∀ Q : ℕ → Prop, IsPi01 Q → ManyOneReducible Q P

structure UniversalInput where
  run : ℕ →. ℕ
  run_partrec : Partrec run
  compile : Nat.Partrec.Code → ℕ
  compile_computable : Computable compile
  compile_spec : ∀ e, (run (compile e)).Dom ↔ (Nat.Partrec.Code.eval e 0).Dom

structure Data where
  c : ℚ
  c_pos : 0 < c
  L0 : ℕ → ℕ
  lo : ℕ → ℚ
  hi : ℕ → ℚ
  window : ∀ n, 0 < lo n ∧ lo n < hi n ∧ hi n < 1
  disjoint : ∀ n m, n ≠ m → hi n ≤ lo m ∨ hi m ≤ lo n
  polynomial : ℕ → ℕ → ℕ → Polynomial ℚ
  rate : ℕ → ℚ
  rate_surjective : Function.Surjective rate
  test : ℕ × (ℕ × (ℕ × ℕ)) → Bool
  test_computable : Computable test
  -- The computable test accepts inadmissible triples, and otherwise performs
  -- exactly the rational comparison in the paper; no finite-precision oracle.
  test_spec : ∀ n L t k, test (n, L, t, k) = true ↔
    (L0 n ≤ L ∧ (t : ℚ) ≤ c * (L : ℚ) ∧ lo n < rate k ∧ rate k < hi n →
      (7 / 8 : ℚ) ≤ (polynomial n L t).eval (rate k))

def RationalCertificate (d : Data) (n : ℕ) : Prop :=
  ∀ (L t : ℕ) (q : ℚ), d.L0 n ≤ L → (t : ℚ) ≤ d.c * (L : ℚ) →
    d.lo n < q → q < d.hi n → (7 / 8 : ℚ) ≤ (d.polynomial n L t).eval q

noncomputable def RealCertificate (d : Data) (n : ℕ) : Prop :=
  ∀ (L t : ℕ) (x : ℝ), d.L0 n ≤ L → (t : ℚ) ≤ d.c * (L : ℚ) →
    (d.lo n : ℝ) < x → x < (d.hi n : ℝ) →
      (7 / 8 : ℝ) ≤ ((d.polynomial n L t).map (algebraMap ℚ ℝ)).eval x

-- These are the current paper's own physical inputs, not imported theorems.
def StorageInput (u : UniversalInput) (d : Data) : Prop :=
  ∀ n, ¬ (u.run n).Dom → ∀ (L t : ℕ) (q : ℚ),
    d.L0 n ≤ L → (t : ℚ) ≤ d.c * (L : ℚ) → d.lo n < q → q < d.hi n →
      (15 / 16 : ℚ) ≤ (d.polynomial n L t).eval q

def ForgettingInput (u : UniversalInput) (d : Data) : Prop :=
  ∀ n, (u.run n).Dom → ∃ T : ℕ, ∀ (L t : ℕ) (q : ℚ),
    T ≤ t → d.lo n < q → q < d.hi n →
      (d.polynomial n L t).eval q ≤ (9 / 16 : ℚ)

/-- Conditional abstract form of v2 Theorem 8.2, NOT an unconditional
formalization of the three-dimensional medium.  The inequality t <= c L
is exactly t <= floor(c L) for natural t and positive rational c. -/
theorem abstract_window_certification
    (u : UniversalInput) (d : Data)
    (hStorage : StorageInput u d) (hForgetting : ForgettingInput u d) :
    (∀ n, RationalCertificate d n ↔ ¬ (u.run n).Dom) ∧
    IsPi01Complete (RationalCertificate d) ∧
    (∀ n, RationalCertificate d n ↔ RealCertificate d n) ∧
    ¬ ComputablePred (RationalCertificate d) := by
  sorry


end CertificationScope
