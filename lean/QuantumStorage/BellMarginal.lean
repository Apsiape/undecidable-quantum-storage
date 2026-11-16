import QuantumStorage.BellFoundation
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-- The partial trace over the second finite tensor factor. -/
noncomputable def partialTraceRight {α γ : Type} [Fintype γ]
    (ρ : Mat (α × γ)) : Mat α := fun x y => ∑ z : γ, ρ (x, z) (y, z)

noncomputable def partialTraceRightQ (α γ : Type) [Fintype α] [Fintype γ] :
    QMap (α × γ) α where
  toFun := partialTraceRight
  map_add' ρ σ := by ext x y; simp [partialTraceRight, Finset.sum_add_distrib]
  map_smul' c ρ := by ext x y; simp [partialTraceRight, Finset.mul_sum]

/-- A change of finite orthonormal basis, as an actual matrix channel. -/
noncomputable def reindexQ {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) : QMap α β where
  toFun ρ := ρ.submatrix e.symm e.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reindexQ_cptp {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) :
    IsCPTP (reindexQ e) := by
  constructor
  · intro ρ
    exact e.symm.sum_comp (fun x => ρ x x)
  · intro r ρ hρ
    exact hρ.submatrix (fun x : Fin r × β => (x.1, e.symm x.2))

theorem partialTraceRight_trace {α γ : Type} [Fintype α] [Fintype γ]
    (ρ : Mat (α × γ)) : Matrix.trace (partialTraceRight ρ) = Matrix.trace ρ := by
  simp [Matrix.trace, Matrix.diag, partialTraceRight, Fintype.sum_prod_type]

theorem partialTraceRight_posSemidef {α γ : Type} [Fintype γ]
    (ρ : Mat (α × γ)) (hρ : ρ.PosSemidef) : (partialTraceRight ρ).PosSemidef := by
  have h : partialTraceRight ρ =
      ∑ z : γ, ρ.submatrix (fun x => (x, z)) (fun x => (x, z)) := by
    ext x y
    simp [partialTraceRight, Matrix.submatrix, Matrix.sum_apply]
  rw [h]
  exact Matrix.posSemidef_sum Finset.univ (fun z _ => hρ.submatrix _)

theorem partialTraceRightQ_cptp (α γ : Type) [Fintype α] [Fintype γ] :
    IsCPTP (partialTraceRightQ α γ) := by
  constructor
  · exact partialTraceRight_trace
  · intro r ρ hρ
    have h : amplify r (partialTraceRightQ α γ) ρ =
        ∑ z : γ, ρ.submatrix (fun x => (x.1, (x.2, z)))
          (fun x => (x.1, (x.2, z))) := by
      ext x y
      simp [amplify, partialTraceRightQ, partialTraceRight, Matrix.sum_apply]
    rw [h]
    exact Matrix.posSemidef_sum Finset.univ (fun z _ => hρ.submatrix _)

/-- Split one coordinate from the remaining output tensor factors. -/
noncomputable def splitOutput {β : Type} (k : ℕ) (j : Fin k) :
    (Fin k → β) ≃ β × ({i : Fin k // i ≠ j} → β) := Equiv.funSplitAt j β

theorem splitOutput_symm_same {β : Type} (k : ℕ) (j : Fin k)
    (x : β) (w : {i : Fin k // i ≠ j} → β) :
    (splitOutput k j).symm (x, w) j = x := by
  simp [splitOutput, Equiv.funSplitAt, Equiv.piSplitAt]

theorem splitOutput_symm_update {β : Type} (k : ℕ) (j : Fin k)
    (x y : β) (w : {i : Fin k // i ≠ j} → β) :
    Function.update ((splitOutput k j).symm (x, w)) j y =
      (splitOutput k j).symm (y, w) := by
  classical
  funext i
  by_cases h : i = j
  · subst i; simp [splitOutput_symm_same]
  · simp [Function.update, splitOutput, Equiv.funSplitAt, Equiv.piSplitAt, h]

/-- The frozen update-and-sum marginal is exactly the usual partial trace. -/
theorem marginal_eq_partialTraceRight {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) (ρ : Mat (Fin k → β)) :
    marginal k j ρ = partialTraceRight (reindexQ (splitOutput k j) ρ) := by
  classical
  ext x y
  unfold marginal
  rw [← (splitOutput k j).symm.sum_comp]
  simp only [Fintype.sum_prod_type, splitOutput_symm_same]
  simp [partialTraceRight, reindexQ, splitOutput_symm_update]

noncomputable def marginalQ {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) : QMap (Fin k → β) β :=
  (partialTraceRightQ β ({i : Fin k // i ≠ j} → β)).comp
    (reindexQ (splitOutput k j))

theorem marginalQ_apply {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) (ρ : Mat (Fin k → β)) :
    marginalQ k j ρ = marginal k j ρ :=
  (marginal_eq_partialTraceRight k j ρ).symm

theorem marginalQ_cptp {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) : IsCPTP (marginalQ (β := β) k j) :=
  (partialTraceRightQ_cptp _ _).comp (reindexQ_cptp _)

theorem marginal_trace {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) (ρ : Mat (Fin k → β)) :
    Matrix.trace (marginal k j ρ) = Matrix.trace ρ := by
  rw [← marginalQ_apply]
  exact (marginalQ_cptp k j).1 ρ

theorem marginal_posSemidef {β : Type} [Fintype β] [DecidableEq β]
    (k : ℕ) (j : Fin k) (ρ : Mat (Fin k → β)) (hρ : ρ.PosSemidef) :
    (marginal k j ρ).PosSemidef := by
  rw [marginal_eq_partialTraceRight]
  exact partialTraceRight_posSemidef _ (hρ.submatrix _)

/-- Full-channel marginal equality also holds with an arbitrary reference. -/
theorem amplify_marginal_comp {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (r k : ℕ) (j : Fin k) (S : QMap α (Fin k → β)) (T : QMap α β)
    (h : ∀ ρ, marginal k j (S ρ) = T ρ) (ρ : Mat (Fin r × α)) :
    amplify r (marginalQ k j) (amplify r S ρ) = amplify r T ρ := by
  ext x y
  change marginalQ k j (S (fun a b => ρ (x.1, a) (y.1, b))) x.2 y.2 = _
  rw [marginalQ_apply, h]
  rfl

end QuantumScope
