import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce
import Mathlib.Analysis.Polynomial.Basic

/- Frozen release challenge. The two target proofs are intentionally omitted. -/
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
