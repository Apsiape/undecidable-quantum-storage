import QuantumStorage.Definitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-- Block amplification respects composition of the actual matrix maps. -/
theorem amplify_comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (r : ℕ) (T : QMap α β) (U : QMap β γ) (ρ : Mat (Fin r × α)) :
    amplify r (U.comp T) ρ = amplify r U (amplify r T ρ) := rfl

theorem IsCPTP.comp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    {T : QMap α β} {U : QMap β γ} (hU : IsCPTP U) (hT : IsCPTP T) :
    IsCPTP (U.comp T) := by
  constructor
  · intro ρ
    exact (hU.1 (T ρ)).trans (hT.1 ρ)
  · intro r ρ hρ
    rw [amplify_comp]
    exact hU.2 r _ (hT.2 r ρ hρ)

/-- Trace preservation also holds with the untouched reference present. -/
theorem trace_amplify {α β : Type} [Fintype α] [Fintype β]
    (r : ℕ) (T : QMap α β) (hT : ∀ ρ, Matrix.trace (T ρ) = Matrix.trace ρ)
    (ρ : Mat (Fin r × α)) : Matrix.trace (amplify r T ρ) = Matrix.trace ρ := by
  classical
  calc
    Matrix.trace (amplify r T ρ) =
        ∑ i : Fin r, Matrix.trace (T (fun x y => ρ (i, x) (i, y))) := by
      simp [Matrix.trace, Matrix.diag, amplify, Fintype.sum_prod_type]
    _ = ∑ i : Fin r, Matrix.trace (fun x y => ρ (i, x) (i, y)) := by simp_rw [hT]
    _ = Matrix.trace ρ := by simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

theorem bell_trace : Matrix.trace bell = 1 := by
  norm_num [Matrix.trace, bell, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem bell_conjTranspose : bell.conjTranspose = bell := by
  ext u v
  simp only [Matrix.conjTranspose_apply, bell]
  split_ifs <;> simp_all

theorem bell_mul_self : bell * bell = bell := by
  ext ⟨i, j⟩ ⟨m, n⟩
  fin_cases i <;> fin_cases j <;> fin_cases m <;> fin_cases n <;>
    norm_num [bell, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem bell_posSemidef : bell.PosSemidef := by
  let A : Matrix Unit (Fin 2 × Fin 2) ℂ := fun _ u => if u.1 = u.2 then 1 else 0
  have heq : bell = (1 / 2 : ℝ) • (A.conjTranspose * A) := by
    ext ⟨i, j⟩ ⟨m, n⟩
    fin_cases i <;> fin_cases j <;> fin_cases m <;> fin_cases n <;>
      norm_num [bell, A, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self A).smul (by norm_num)

theorem one_sub_bell_posSemidef : (1 - bell).PosSemidef := by
  have heq : (1 - bell).conjTranspose * (1 - bell) = 1 - bell := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, bell_conjTranspose]
    calc
      (1 - bell) * (1 - bell) = 1 - bell - bell + bell * bell := by noncomm_ring
      _ = 1 - bell := by rw [bell_mul_self]; abel
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - bell)

/-- The frozen Bell reference becomes a positive trace-one joint state after
any CPTP encoded, transmitted, and decoded channel. -/
theorem encoded_bell_state {α β : Type} [Fintype α] [Fintype β]
    (E : QMap (Fin 2) α) (T : QMap α β) (D : QMap β (Fin 2))
    (hE : IsCPTP E) (hT : IsCPTP T) (hD : IsCPTP D) :
    (amplify 2 (D.comp (T.comp E)) bell).PosSemidef ∧
    Matrix.trace (amplify 2 (D.comp (T.comp E)) bell) = 1 := by
  have h := hD.comp (hT.comp hE)
  exact ⟨h.2 2 bell bell_posSemidef, (trace_amplify 2 _ h.1 bell).trans bell_trace⟩

/-- A projection has nonnegative expectation in every positive matrix. -/
theorem projection_expectation_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    (P ρ : Mat ι) (hP : P.conjTranspose = P) (hPP : P * P = P)
    (hρ : ρ.PosSemidef) : 0 ≤ (Matrix.trace (P * ρ)).re := by
  have hh := (hρ.mul_mul_conjTranspose_same P).trace_nonneg
  rw [hP, Matrix.trace_mul_cycle, hPP] at hh
  exact (RCLike.nonneg_iff.mp hh).1

/-- Basic fidelity bounds, including the k=1 endpoint of the frozen target. -/
theorem entanglementFidelity_bounds {α β : Type} [Fintype α] [Fintype β]
    (E : QMap (Fin 2) α) (T : QMap α β) (D : QMap β (Fin 2))
    (hE : IsCPTP E) (hT : IsCPTP T) (hD : IsCPTP D) :
    0 ≤ entanglementFidelity E T D ∧ entanglementFidelity E T D ≤ 1 := by
  obtain ⟨hρ, htr⟩ := encoded_bell_state E T D hE hT hD
  have hlo := projection_expectation_nonneg bell _ bell_conjTranspose bell_mul_self hρ
  have hQ : (1 - bell).conjTranspose = 1 - bell := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, bell_conjTranspose]
  have hQQ : (1 - bell) * (1 - bell) = 1 - bell := by
    calc
      (1 - bell) * (1 - bell) = 1 - bell - bell + bell * bell := by noncomm_ring
      _ = 1 - bell := by rw [bell_mul_self]; abel
  have hhi := projection_expectation_nonneg (1 - bell) _ hQ hQQ hρ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htr] at hhi
  dsimp [entanglementFidelity]
  exact ⟨hlo, by simpa using hhi⟩

end QuantumScope
