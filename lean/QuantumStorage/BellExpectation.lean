import QuantumStorage.BellInsertion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-- Tensor a finite observable with the identity on the traced-out factor. -/
noncomputable def liftRight {α γ : Type} (H : Mat α) : Mat (α × γ) := by
  classical
  exact fun u v => H u.1 v.1 * if u.2 = v.2 then 1 else 0

theorem trace_liftRight {α γ : Type} [Fintype α] [Fintype γ]
    (H : Mat α) (ρ : Mat (α × γ)) :
    Matrix.trace (liftRight H * ρ) = Matrix.trace (H * partialTraceRight ρ) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    liftRight, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [partialTraceRight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]

noncomputable def bellSplit (k : ℕ) (j : Fin k) : BellSpace k ≃
    (Fin 2 × Fin 2) × ({i : Fin k // i ≠ j} → Fin 2) :=
  (Equiv.prodCongr (Equiv.refl _) (splitOutput k j)).trans (Equiv.prodAssoc _ _ _).symm

noncomputable def bellProjector (k : ℕ) (j : Fin k) : Mat (BellSpace k) :=
  reindexQ (bellSplit k j).symm (liftRight bell)

theorem bellProjector_apply (k : ℕ) (j : Fin k) (u v : BellSpace k) :
    bellProjector k j u v =
      (if u.1 = u.2 j ∧ v.1 = v.2 j then (1 / 2 : ℂ) else 0) *
        if (splitOutput k j u.2).2 = (splitOutput k j v.2).2 then 1 else 0 := by
  simp [bellProjector, reindexQ, bellSplit, liftRight, bell,
    splitOutput, Equiv.funSplitAt, Equiv.piSplitAt, Matrix.submatrix]

theorem reindexQ_mul {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (H ρ : Mat α) :
    reindexQ e H * reindexQ e ρ = reindexQ e (H * ρ) :=
  Matrix.submatrix_mul_equiv H ρ e.symm e.symm e.symm

theorem bell_reference_marginal_split (k : ℕ) (j : Fin k) (ρ : Mat (BellSpace k)) :
    amplify 2 (marginalQ k j) ρ =
      partialTraceRight (reindexQ (bellSplit k j) ρ) := by
  rfl

/-- Each Bell-projector expectation equals the exact frozen Bell overlap of
that reference/output marginal. -/
theorem trace_bellProjector (k : ℕ) (j : Fin k) (ρ : Mat (BellSpace k)) :
    Matrix.trace (bellProjector k j * ρ) =
      Matrix.trace (bell * amplify 2 (marginalQ k j) ρ) := by
  have hρ : reindexQ (bellSplit k j).symm (reindexQ (bellSplit k j) ρ) = ρ := by
    ext u v; simp [reindexQ, Matrix.submatrix]
  calc
    Matrix.trace (bellProjector k j * ρ) =
        Matrix.trace (reindexQ (bellSplit k j).symm
          (liftRight bell * reindexQ (bellSplit k j) ρ)) := by
      rw [← reindexQ_mul, hρ]
      rfl
    _ = Matrix.trace (liftRight bell * reindexQ (bellSplit k j) ρ) :=
      (reindexQ_cptp _).1 _
    _ = Matrix.trace (bell * amplify 2 (marginalQ k j) ρ) := by
      rw [trace_liftRight, bell_reference_marginal_split]

theorem bellInsertion_projectors (k : ℕ) :
    bellInsertion k * (bellInsertion k).conjTranspose =
      (2 : ℝ) • ∑ j : Fin k, bellProjector k j := by
  classical
  ext u v
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, bellInsertion_star,
    Fintype.sum_sigma, Matrix.smul_apply, Matrix.sum_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [bellProjector_apply]
  by_cases hu : u.2 j = u.1
  · by_cases hv : v.2 j = v.1
    · simp only [bellInsertion, hu, hv, true_and]
      simp only [ite_mul, one_mul, zero_mul]
      trans (if (splitOutput k j v.2).2 = (splitOutput k j u.2).2 then (1 : ℂ) else 0)
      · exact Finset.sum_ite_eq_of_mem Finset.univ _
          (fun w => if (splitOutput k j v.2).2 = w then (1 : ℂ) else 0) (Finset.mem_univ _)
      · by_cases hw : (splitOutput k j u.2).2 = (splitOutput k j v.2).2
        · simp [hw, eq_comm]
        · simp [hw, Ne.symm hw]
    · simp [bellInsertion, hv, Ne.symm hv]
  · simp [bellInsertion, hu, Ne.symm hu]

/-- The full normalized Bell-sharing operator bound. -/
theorem bellProjector_sum_bound (k : ℕ) :
    ((((k : ℝ) + 1) / 2) • (1 : Mat (BellSpace k)) -
      ∑ j : Fin k, bellProjector k j).PosSemidef := by
  have h := (bellInsertion_bound k).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [bellInsertion_projectors] at h
  simpa only [smul_sub, smul_smul, one_div_mul_eq_div, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
    one_smul] using h

/-- The Bell-sharing state estimate for every positive trace-one finite state. -/
theorem bellProjector_state_bound (k : ℕ) (ρ : Mat (BellSpace k))
    (hρ : ρ.PosSemidef) (hTrace : Matrix.trace ρ = 1) :
    (∑ j : Fin k, (Matrix.trace (bellProjector k j * ρ)).re) ≤ ((k : ℝ) + 1) / 2 := by
  classical
  have h := positive_trace_pairing _ ρ (bellProjector_sum_bound k) hρ
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.sum_mul,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_sum, Complex.sub_re, Complex.re_sum,
    Complex.real_smul, Complex.ofReal_re, hTrace, mul_one] at h
  linarith

end QuantumScope
