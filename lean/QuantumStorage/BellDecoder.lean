import QuantumStorage.BellTensor
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

noncomputable def partialTraceLeft {α γ : Type} [Fintype α]
    (ρ : Mat (α × γ)) : Mat γ := fun x y => ∑ z : α, ρ (z, x) (z, y)

theorem partialTraceLeft_firstQ {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (T : QMap α β) (hT : ∀ ρ, Matrix.trace (T ρ) = Matrix.trace ρ)
    (ρ : Mat (α × γ)) : partialTraceLeft (firstQ T ρ) = partialTraceLeft ρ := by
  ext x y
  exact hT (fun a b => ρ (a, x) (b, y))

theorem partialTraceLeft_amplifyAnyQ {α γ δ : Type}
    [Fintype α] [Fintype γ] [Fintype δ]
    (U : QMap γ δ) (ρ : Mat (α × γ)) :
    partialTraceLeft (amplifyAnyQ α U ρ) = U (partialTraceLeft ρ) := by
  have h : partialTraceLeft ρ = ∑ z : α, (fun a b => ρ (z, a) (z, b)) := by
    ext a b; simp [partialTraceLeft]
  rw [h, map_sum]
  ext x y
  simp [partialTraceLeft, amplifyAnyQ, Matrix.sum_apply]

theorem partialTraceLeft_tensorQ {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (T : QMap α β) (U : QMap γ δ)
    (hT : ∀ ρ, Matrix.trace (T ρ) = Matrix.trace ρ) (ρ : Mat (α × γ)) :
    partialTraceLeft (tensorQ T U ρ) = U (partialTraceLeft ρ) := by
  change partialTraceLeft (firstQ T (amplifyAnyQ α U ρ)) = _
  rw [partialTraceLeft_firstQ T hT, partialTraceLeft_amplifyAnyQ]

def tupleSplit (k : ℕ) (β : Type) : (Fin (k + 1) → β) ≃ β × (Fin k → β) :=
  (Fin.consEquiv (fun _ => β)).symm

/-- Apply the common decoder independently to all k output factors. -/
noncomputable def tensorPowerQ {β γ : Type} [Fintype β] [Fintype γ]
    (D : QMap β γ) : (k : ℕ) → QMap (Fin k → β) (Fin k → γ)
  | 0 => reindexQ (Equiv.ofUnique _ _)
  | k + 1 => (reindexQ (tupleSplit k γ).symm).comp
      ((tensorQ D (tensorPowerQ D k)).comp (reindexQ (tupleSplit k β)))

theorem tensorPowerQ_cptp {β γ : Type} [Fintype β] [Fintype γ]
    (D : QMap β γ) (hD : IsCPTP D) (k : ℕ) : IsCPTP (tensorPowerQ D k) := by
  induction k with
  | zero => exact reindexQ_cptp _
  | succ k ih => exact (reindexQ_cptp _).comp ((tensorQ_cptp D _ hD ih).comp
      (reindexQ_cptp _))

theorem marginal_zero_cons {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (ρ : Mat (β × (Fin k → β))) :
    marginal (k + 1) 0 (reindexQ (tupleSplit k β).symm ρ) = partialTraceRight ρ := by
  classical
  ext x y
  unfold marginal
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => β)).sum_comp]
  simp [Fintype.sum_prod_type, reindexQ, tupleSplit, Fin.consEquiv,
    Fin.update_cons_zero, partialTraceRight, Matrix.submatrix]

theorem marginal_succ_cons {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) (ρ : Mat (β × (Fin k → β))) :
    marginal (k + 1) j.succ (reindexQ (tupleSplit k β).symm ρ) =
      marginal k j (partialTraceLeft ρ) := by
  classical
  ext x y
  unfold marginal
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => β)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_succ]
  simp_rw [← Fin.cons_update]
  simp [reindexQ, tupleSplit, Fin.consEquiv, Matrix.submatrix, partialTraceLeft]
  rw [Finset.sum_comm]
  simp [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)), Finset.sum_ite_irrel]

/-- All decoded marginals are D applied to the original full-channel marginal. -/
theorem marginal_tensorPowerQ {β γ : Type}
    [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (D : QMap β γ) (hD : IsCPTP D) (k : ℕ) (j : Fin k)
    (ρ : Mat (Fin k → β)) :
    marginal k j (tensorPowerQ D k ρ) = D (marginal k j ρ) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    let σ := reindexQ (tupleSplit k β) ρ
    have hρ : reindexQ (tupleSplit k β).symm σ = ρ := by
      ext x y; simp [σ, reindexQ, Matrix.submatrix]
    change marginal (k + 1) j
      (reindexQ (tupleSplit k γ).symm (tensorQ D (tensorPowerQ D k) σ)) = _
    induction j using Fin.cases with
    | zero =>
      rw [marginal_zero_cons, partialTraceRight_tensorQ D _ (tensorPowerQ_cptp D hD k).1]
      conv_rhs => rw [← hρ, marginal_zero_cons]
    | succ j =>
      rw [marginal_succ_cons, partialTraceLeft_tensorQ D _ hD.1, ih]
      conv_rhs => rw [← hρ, marginal_succ_cons]

/-- Encoding the input and independently decoding every output preserves the
entire equal-marginal extension property, on every input matrix. -/
theorem decoded_equalMarginalExtension {α β : Type}
    [Fintype α] [Fintype β] [DecidableEq β]
    (k : ℕ) (T : QMap α β) (hExt : HasEqualMarginalExtension k T)
    (E : QMap (Fin 2) α) (hE : IsCPTP E)
    (D : QMap β (Fin 2)) (hD : IsCPTP D) :
    HasEqualMarginalExtension k (D.comp (T.comp E)) := by
  obtain ⟨S, hS, hMarg⟩ := hExt
  refine ⟨(tensorPowerQ D k).comp (S.comp E),
    (tensorPowerQ_cptp D hD k).comp (hS.comp hE), ?_⟩
  intro j ρ
  change marginal k j (tensorPowerQ D k (S (E ρ))) = D (T (E ρ))
  rw [marginal_tensorPowerQ D hD, hMarg]

/-- The decoded extension's Bell-reference state is positive and trace one;
its reference/output marginals are exactly the frozen amplified channel. -/
theorem decoded_reference_state {α β : Type}
    [Fintype α] [Fintype β] [DecidableEq β]
    (k : ℕ) (T : QMap α β) (hExt : HasEqualMarginalExtension k T)
    (E : QMap (Fin 2) α) (hE : IsCPTP E)
    (D : QMap β (Fin 2)) (hD : IsCPTP D) :
    ∃ ρ : Mat (Fin 2 × (Fin k → Fin 2)), ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      ∀ j : Fin k, amplify 2 (marginalQ k j) ρ =
        amplify 2 (D.comp (T.comp E)) bell := by
  obtain ⟨S, hS, hMarg⟩ := decoded_equalMarginalExtension k T hExt E hE D hD
  refine ⟨amplify 2 S bell, hS.2 2 bell bell_posSemidef,
    (trace_amplify 2 S hS.1 bell).trans bell_trace, ?_⟩
  intro j
  exact amplify_marginal_comp 2 k j S _ (hMarg j) bell

end QuantumScope
