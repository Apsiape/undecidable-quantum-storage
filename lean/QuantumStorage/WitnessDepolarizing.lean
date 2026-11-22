import QuantumStorage.Depolarizing

/-! A satisfiability witness whose extension branch is not a replacement
(audit 1, P3-6): the half-depolarizing channel (1/2) R_σ + (1/2) id has a
two-output equal-marginal extension (append a fresh σ, then symmetrize the two
outputs), and with it every hypothesis of `uniform_forgetting` is discharged on a
qubit with a nonempty small part and a nonempty large part. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
namespace QuantumScope

theorem marginal_add' {β : Type} [Fintype β] [DecidableEq β] (k : ℕ) (j : Fin k)
    (A B : Mat (Fin k → β)) : marginal k j (A + B) = marginal k j A + marginal k j B := by
  rw [← marginalQ_apply, map_add, marginalQ_apply, marginalQ_apply]

theorem marginal_smul' {β : Type} [Fintype β] [DecidableEq β] (k : ℕ) (j : Fin k) (c : ℂ)
    (A : Mat (Fin k → β)) : marginal k j (c • A) = c • marginal k j A := by
  rw [← marginalQ_apply, map_smul, marginalQ_apply]

/-- Permuting the outputs permutes the marginals. -/
theorem marginal_reindex_perm {β : Type} [Fintype β] [DecidableEq β] (k : ℕ)
    (e : Fin k ≃ Fin k) (j : Fin k) (ρ : Mat (Fin k → β)) :
    marginal k j (reindexQ (Equiv.arrowCongr e (Equiv.refl β)) ρ) = marginal k (e.symm j) ρ := by
  ext x y
  unfold marginal
  rw [← (Equiv.arrowCongr e (Equiv.refl β)).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  have h1 : (Equiv.arrowCongr e (Equiv.refl β)) u j = u (e.symm j) := rfl
  have h2 : (Equiv.arrowCongr e (Equiv.refl β)).symm
      (Function.update ((Equiv.arrowCongr e (Equiv.refl β)) u) j y) =
        Function.update u (e.symm j) y := by
    funext i
    by_cases h : i = e.symm j
    · subst h
      simp [Equiv.arrowCongr_apply]
    · have h' : e i ≠ j := fun hh => h (by rw [← hh, Equiv.symm_apply_apply])
      simp [Equiv.arrowCongr_apply, Function.update_of_ne h', Function.update_of_ne h]
  simp only [reindexQ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, h1, h2]

/-- The one-output marginal of a relabelled matrix. -/
theorem marginal_one_funUnique {β : Type} [Fintype β] [DecidableEq β] (σ : Mat β) :
    marginal 1 0 (reindexQ (Equiv.funUnique (Fin 1) β).symm σ) = σ := by
  ext x y
  unfold marginal
  rw [← (Equiv.funUnique (Fin 1) β).symm.sum_comp]
  simp [reindexQ, Matrix.submatrix_apply]

/-- Append a fresh copy of σ as a second output: ρ ↦ ρ ⊗ σ. -/
noncomputable def appendQ {β : Type} [Fintype β] (σ : Mat β) : QMap β (Fin 2 → β) :=
  (reindexQ (tupleSplit 1 β).symm).comp
    ((tensorQ (LinearMap.id : QMap β β)
      (replaceQ (reindexQ (Equiv.funUnique (Fin 1) β).symm σ) : QMap PUnit (Fin 1 → β))).comp
      (reindexQ (Equiv.prodPUnit β).symm))

theorem appendQ_cptp {β : Type} [Fintype β] (σ : Mat β) (hσ : σ.PosSemidef)
    (hσ1 : Matrix.trace σ = 1) : IsCPTP (appendQ σ) := by
  have hτ : (reindexQ (Equiv.funUnique (Fin 1) β).symm σ).PosSemidef := hσ.submatrix _
  have hτ1 : Matrix.trace (reindexQ (Equiv.funUnique (Fin 1) β).symm σ) = 1 := by
    rw [(reindexQ_cptp _).1, hσ1]
  exact (reindexQ_cptp _).comp ((tensorQ_cptp _ _ isCPTP_id (replaceQ_cptp _ hτ hτ1)).comp
    (reindexQ_cptp _))

theorem appendQ_marginal_zero {β : Type} [Fintype β] [DecidableEq β] (σ : Mat β)
    (hσ1 : Matrix.trace σ = 1) (ρ : Mat β) : marginal 2 0 (appendQ σ ρ) = ρ := by
  have hτ1 : Matrix.trace (reindexQ (Equiv.funUnique (Fin 1) β).symm σ) = 1 := by
    rw [(reindexQ_cptp _).1, hσ1]
  have hR : ∀ ρ' : Mat PUnit, Matrix.trace
      ((replaceQ (reindexQ (Equiv.funUnique (Fin 1) β).symm σ) : QMap PUnit (Fin 1 → β)) ρ') =
        Matrix.trace ρ' := by
    intro ρ'
    rw [replaceQ_apply, Matrix.trace_smul, hτ1, smul_eq_mul, mul_one]
  change marginal (1 + 1) 0 (reindexQ (tupleSplit 1 β).symm
    (tensorQ LinearMap.id _ (reindexQ (Equiv.prodPUnit β).symm ρ))) = ρ
  rw [marginal_zero_cons, partialTraceRight_tensorQ _ _ hR, LinearMap.id_apply]
  ext x y
  simp [partialTraceRight, reindexQ, Matrix.submatrix_apply]

theorem appendQ_marginal_one {β : Type} [Fintype β] [DecidableEq β] (σ : Mat β)
    (ρ : Mat β) : marginal 2 1 (appendQ σ ρ) = Matrix.trace ρ • σ := by
  change marginal (1 + 1) (0 : Fin 1).succ (reindexQ (tupleSplit 1 β).symm
    (tensorQ LinearMap.id _ (reindexQ (Equiv.prodPUnit β).symm ρ))) = _
  rw [marginal_succ_cons, partialTraceLeft_tensorQ _ _ (fun _ => rfl), replaceQ_apply,
    marginal_smul', marginal_one_funUnique]
  congr 1
  simp [partialTraceLeft, reindexQ, Matrix.submatrix_apply, Matrix.trace]

/-- The output swap on two outputs. -/
def swapOutputs (β : Type) : (Fin 2 → β) ≃ (Fin 2 → β) :=
  Equiv.arrowCongr (Equiv.swap 0 1) (Equiv.refl β)

/-- The half-depolarizing channel (1/2) R_σ + (1/2) id has a two-output
equal-marginal extension: the symmetrization of "append a fresh σ". -/
theorem halfDepolarizing_extension {β : Type} [Fintype β] [DecidableEq β] (σ : Mat β)
    (hσ : σ.PosSemidef) (hσ1 : Matrix.trace σ = 1) (Λ : QMap β β)
    (hΛ : ∀ ρ, Λ ρ = (((1 / 2 : ℝ)) : ℂ) • (Matrix.trace ρ • σ) +
      (1 - (((1 / 2 : ℝ)) : ℂ)) • ρ) :
    HasEqualMarginalExtension 2 Λ := by
  have hA := appendQ_cptp σ hσ hσ1
  refine ⟨((1 / 2 : ℝ) : ℂ) • appendQ σ +
      ((1 / 2 : ℝ) : ℂ) • (reindexQ (swapOutputs β)).comp (appendQ σ),
    isCPTP_combo _ _ (by norm_num) (by norm_num) (by norm_num) _ _ hA
      ((reindexQ_cptp _).comp hA), ?_⟩
  intro j ρ
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    marginal_add', marginal_smul', marginal_smul', swapOutputs, marginal_reindex_perm, hΛ]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Equiv.symm_swap, Equiv.swap_apply_left]
    rw [appendQ_marginal_zero σ hσ1, appendQ_marginal_one]
    push_cast
    ring_nf
    rw [add_comm]
  · simp only [Fin.mk_one, Fin.isValue, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [appendQ_marginal_zero σ hσ1, appendQ_marginal_one]
    push_cast
    ring_nf

/-- The half-depolarizing qubit channel (1/2) R_{I/2} + (1/2) id. -/
noncomputable def halfDepolarizingQubit : QMap (Fin 2) (Fin 2) :=
  ((1 / 2 : ℝ) : ℂ) • replaceQ (maxMixed (Fin 2)) +
    ((1 / 2 : ℝ) : ℂ) • (LinearMap.id : QMap (Fin 2) (Fin 2))

theorem halfDepolarizingQubit_apply (ρ : Mat (Fin 2)) :
    halfDepolarizingQubit ρ = (((1 / 2 : ℝ)) : ℂ) • (Matrix.trace ρ • maxMixed (Fin 2)) +
      (1 - (((1 / 2 : ℝ)) : ℂ)) • ρ := by
  rw [halfDepolarizingQubit, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    replaceQ_apply]
  congr 1
  norm_num

theorem halfDepolarizingQubit_cptp : IsCPTP halfDepolarizingQubit :=
  isCPTP_combo _ _ (by norm_num) (by norm_num) (by norm_num) _ _
    (replaceQ_cptp _ (maxMixed_posSemidef _) (maxMixed_trace _)) isCPTP_id

/-- Satisfiability with a non-replacement channel on both parts: the
half-depolarizing qubit channel meets the extension hypothesis (large part {false},
s = 1) and the replacement decomposition with q = p = 1/2 (small part {true}). -/
theorem uniform_forgetting_instance_depolarizing (η : ℝ) (hη : 0 < η) :
    ∃ C : ℕ, ∀ (_ : Bool) (t : ℕ), C ≤ t →
      ∀ M : QMap (Fin 2) (Fin 2), IsCPTP M →
      ∀ E : QMap (Fin 2) (Fin 2), IsCPTP E →
      ∀ D : QMap (Fin 2) (Fin 2), IsCPTP D →
        entanglementFidelity E (M.comp (halfDepolarizingQubit ^ t)) D ≤ 1 / 2 + η :=
  uniform_forgetting (fun _ : Bool => 2) (fun _ => halfDepolarizingQubit)
    (fun _ => halfDepolarizingQubit_cptp) {true} 1
    (fun _ _ => by
      rw [pow_one]
      exact halfDepolarizing_extension _ (maxMixed_posSemidef _) (maxMixed_trace _) _
        halfDepolarizingQubit_apply)
    (1 / 2) (by norm_num) (by norm_num) (fun _ => 1 / 2) (fun _ => maxMixed (Fin 2))
    (fun _ => LinearMap.id)
    (fun _ _ => ⟨le_rfl, by norm_num, maxMixed_trace _, isCPTP_id,
      fun ρ => halfDepolarizingQubit_apply ρ⟩)
    η hη

end QuantumScope
