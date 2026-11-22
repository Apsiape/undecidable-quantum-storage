import QuantumStorage.UniformForgetting
import Mathlib.Analysis.Matrix.Order

/-! Satisfiability witnesses for the hypothesis bundles of this sprint: the
replacement channel is CPTP, has equal-marginal extensions with any number of
outputs, and instantiates `uniform_forgetting` with a nonempty small part and a
nonempty large part. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
namespace QuantumScope

theorem replaceQ_cptp {α β : Type} [Fintype α] [Fintype β] (σ : Mat β)
    (hσ : σ.PosSemidef) (hσ1 : Matrix.trace σ = 1) :
    IsCPTP (replaceQ σ : QMap α β) := by
  constructor
  · intro ρ
    rw [replaceQ_apply, Matrix.trace_smul, hσ1, smul_eq_mul, mul_one]
  · intro r ρ hρ
    have h : amplify r (replaceQ σ : QMap α β) ρ = (partialTraceRight ρ) ⊗ₖ σ := by
      ext u v
      simp [amplify, replaceQ_apply, Matrix.kroneckerMap_apply, partialTraceRight,
        Matrix.trace, Matrix.diag]
    rw [h]
    exact (partialTraceRight_posSemidef ρ hρ).kronecker hσ

/-- The maximally mixed state. -/
noncomputable def maxMixed (α : Type) [Fintype α] [DecidableEq α] : Mat α :=
  ((Fintype.card α : ℂ)⁻¹) • (1 : Mat α)

theorem maxMixed_posSemidef (α : Type) [Fintype α] [DecidableEq α] :
    (maxMixed α).PosSemidef := by
  have h : (0 : ℂ) ≤ (Fintype.card α : ℂ)⁻¹ := by
    rw [show (Fintype.card α : ℂ)⁻¹ = (((Fintype.card α : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (by positivity)
  exact Matrix.PosSemidef.one.smul h

theorem maxMixed_trace (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    Matrix.trace (maxMixed α) = 1 := by
  have hc : (Fintype.card α : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := α)).ne'
  rw [maxMixed, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, inv_mul_cancel₀ hc]

/-- The full-replacement channel has a k-output equal-marginal extension for
every k: prepare k fresh copies of σ. -/
theorem replaceQ_extension {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (σ : Mat α) (hσ : σ.PosSemidef) (hσ1 : Matrix.trace σ = 1) (k : ℕ) :
    HasEqualMarginalExtension k (replaceQ σ : QMap α α) := by
  have hR := replaceQ_cptp (α := α) σ hσ hσ1
  refine ⟨(tensorPowerQ (replaceQ σ : QMap α α) k).comp
      (replaceQ (maxMixed (Fin k → α))),
    (tensorPowerQ_cptp _ hR k).comp
      (replaceQ_cptp _ (maxMixed_posSemidef _) (maxMixed_trace _)), ?_⟩
  intro j ρ
  rw [LinearMap.comp_apply, marginal_tensorPowerQ _ hR, replaceQ_apply, replaceQ_apply,
    replaceQ_apply, marginal_trace, Matrix.trace_smul, maxMixed_trace, smul_eq_mul, mul_one]

/-- The hypothesis bundle of `uniform_forgetting` is jointly satisfiable, with the
small part {true} and the large part {false} both nonempty: every hypothesis is
discharged for the replacement channel on a qubit. -/
theorem uniform_forgetting_instance (η : ℝ) (hη : 0 < η) :
    ∃ C : ℕ, ∀ (_ : Bool) (t : ℕ), C ≤ t →
      ∀ M : QMap (Fin 2) (Fin 2), IsCPTP M →
      ∀ E : QMap (Fin 2) (Fin 2), IsCPTP E →
      ∀ D : QMap (Fin 2) (Fin 2), IsCPTP D →
        entanglementFidelity E
          (M.comp ((replaceQ (maxMixed (Fin 2)) : QMap (Fin 2) (Fin 2)) ^ t)) D ≤
          1 / 2 + η :=
  uniform_forgetting (fun _ : Bool => 2) (fun _ => replaceQ (maxMixed (Fin 2)))
    (fun _ => replaceQ_cptp _ (maxMixed_posSemidef _) (maxMixed_trace _))
    {true} 1
    (fun _ _ => by
      rw [pow_one]
      exact replaceQ_extension _ (maxMixed_posSemidef _) (maxMixed_trace _) 2)
    1 one_pos le_rfl (fun _ => 1) (fun _ => maxMixed (Fin 2)) (fun _ => LinearMap.id)
    (fun _ _ => ⟨le_rfl, le_rfl, maxMixed_trace _, isCPTP_id, fun ρ => by
      simp [replaceQ_apply]⟩)
    η hη

end QuantumScope
