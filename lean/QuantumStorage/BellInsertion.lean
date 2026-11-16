import QuantumStorage.BellOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

abbrev BellColumn (k : ℕ) := (j : Fin k) × ({i : Fin k // i ≠ j} → Fin 2)
abbrev BellSpace (k : ℕ) := Fin 2 × (Fin k → Fin 2)

/-- Unnormalized Bell insertion; its columns have squared length two. -/
noncomputable def bellInsertion (k : ℕ) : Matrix (BellSpace k) (BellColumn k) ℂ := by
  classical
  exact fun u c => if u.2 c.1 = u.1 ∧ (splitOutput k c.1 u.2).2 = c.2 then 1 else 0

theorem bellInsertion_star (k : ℕ) (u : BellSpace k) (c : BellColumn k) :
    star (bellInsertion k u c) = bellInsertion k u c := by
  simp [bellInsertion]

theorem bellInsertion_nonneg (k : ℕ) (u : BellSpace k) (c : BellColumn k) :
    0 ≤ bellInsertion k u c := by
  unfold bellInsertion
  split_ifs <;> norm_num

theorem bellInsertion_row_sum (k : ℕ) (u : BellSpace k) :
    ∑ c : BellColumn k, bellInsertion k u c =
      ∑ j : Fin k, if u.2 j = u.1 then (1 : ℂ) else 0 := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : u.2 j = u.1
  · simp only [bellInsertion, h, true_and]
    exact Finset.sum_ite_eq_of_mem Finset.univ _ (fun _ => (1 : ℂ)) (Finset.mem_univ _)
  · simp [bellInsertion, h]

/-- A column contracts exactly the two basis states of its Bell insertion. -/
theorem bellInsertion_contract (k : ℕ) (c : BellColumn k) (f : BellSpace k → ℂ) :
    ∑ u : BellSpace k, bellInsertion k u c * f u =
      ∑ r : Fin 2, f (r, (splitOutput k c.1).symm (r, c.2)) := by
  classical
  let e := Equiv.prodCongr (Equiv.refl (Fin 2)) (splitOutput (β := Fin 2) k c.1).symm
  rw [← e.sum_comp]
  simp [e, bellInsertion, Fintype.sum_prod_type, splitOutput_symm_same,
    ite_and, Finset.sum_ite_irrel]

theorem bellInsertion_two_row_sums (k : ℕ) (c : BellColumn k) :
    (∑ r : Fin 2, ∑ j : Fin k,
      if (splitOutput k c.1).symm (r, c.2) j = r then (1 : ℂ) else 0) = k + 1 := by
  classical
  rw [Finset.sum_comm]
  have h : ∀ j : Fin k, (∑ r : Fin 2,
      if (splitOutput k c.1).symm (r, c.2) j = r then (1 : ℂ) else 0) =
      if j = c.1 then 2 else 1 := by
    intro j
    by_cases hj : j = c.1
    · subst j
      simp [splitOutput_symm_same]
    · simp [splitOutput, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  simp_rw [h]
  have he : ∀ j : Fin k, (if j = c.1 then (2 : ℂ) else 1) =
      1 + if j = c.1 then 1 else 0 := by intro j; split_ifs <;> norm_num
  simp_rw [he]
  simp [Finset.sum_add_distrib]

/-- The unnormalized insertion Gram matrix has constant row sum k+1. -/
theorem bellInsertion_gram_row_sum (k : ℕ) (c : BellColumn k) :
    ∑ d : BellColumn k, ((bellInsertion k).conjTranspose * bellInsertion k) c d = k + 1 := by
  classical
  calc
    (∑ d : BellColumn k, ((bellInsertion k).conjTranspose * bellInsertion k) c d) =
        ∑ u : BellSpace k, bellInsertion k u c *
          ∑ d : BellColumn k, bellInsertion k u d := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, bellInsertion_star,
        Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ r : Fin 2, ∑ j : Fin k,
        if (splitOutput k c.1).symm (r, c.2) j = r then (1 : ℂ) else 0 := by
      rw [bellInsertion_contract]
      simp_rw [bellInsertion_row_sum]
    _ = k + 1 := bellInsertion_two_row_sums k c

theorem bellInsertion_gram_nonneg_complex (k : ℕ) (c d : BellColumn k) :
    0 ≤ ((bellInsertion k).conjTranspose * bellInsertion k) c d := by
  classical
  change 0 ≤ ∑ u : BellSpace k, star (bellInsertion k u c) * bellInsertion k u d
  apply Finset.sum_nonneg
  intro u _
  rw [bellInsertion_star]
  exact mul_nonneg (bellInsertion_nonneg k u c) (bellInsertion_nonneg k u d)

theorem bellInsertion_gram_real (k : ℕ) (c d : BellColumn k) :
    ((bellInsertion k).conjTranspose * bellInsertion k) c d =
      ((((bellInsertion k).conjTranspose * bellInsertion k) c d).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using (RCLike.nonneg_iff.mp (bellInsertion_gram_nonneg_complex k c d)).2

theorem bellInsertion_gram_nonneg (k : ℕ) (c d : BellColumn k) :
    0 ≤ (((bellInsertion k).conjTranspose * bellInsertion k) c d).re :=
  (RCLike.nonneg_iff.mp (bellInsertion_gram_nonneg_complex k c d)).1
/-- The finite-qubit insertion operator estimate, derived from its Gram matrix. -/
theorem bellInsertion_bound (k : ℕ) :
    (((k : ℝ) + 1) • (1 : Mat (BellSpace k)) -
      bellInsertion k * (bellInsertion k).conjTranspose).PosSemidef := by
  classical
  apply gram_bound_transfer _ _ (by positivity)
  apply constant_row_sum_posSemidef _ (Matrix.isHermitian_conjTranspose_mul_self _) _
    (bellInsertion_gram_real k) (bellInsertion_gram_nonneg k)
  intro c
  have h := congrArg Complex.re (bellInsertion_gram_row_sum k c)
  simpa using h

end QuantumScope
