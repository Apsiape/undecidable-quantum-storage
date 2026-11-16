import QuantumStorage.BellDecoder
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumScope

/-- Gershgorin proves positivity for a Hermitian diagonally dominant matrix. -/
theorem hermitian_diagonal_dominant_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Mat ι) (hH : H.IsHermitian)
    (hDiag : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖H i j‖ ≤ (H i i).re) :
    H.PosSemidef := by
  apply hH.posSemidef_iff_eigenvalues_nonneg.mpr
  intro l
  change 0 ≤ hH.eigenvalues l
  have hs := spectrum.algebraMap_mem ℂ (hH.eigenvalues_mem_spectrum_real l)
  have hμ : Module.End.HasEigenvalue H.toLin' (hH.eigenvalues l : ℂ) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    simpa only [Matrix.spectrum_toLin', Complex.coe_algebraMap] using hs
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ
  rw [mem_closedBall_iff_norm'] at hi
  have hRe := Complex.re_le_norm (H i i - (hH.eigenvalues l : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hRe
  have hd := hDiag i
  linarith

/-- A nonnegative symmetric weighted Gram matrix with row sum c is bounded
by c times identity; this is the finite weighted-graph Laplacian argument. -/
theorem constant_row_sum_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Mat ι) (hG : G.IsHermitian) (c : ℝ)
    (hReal : ∀ i j, G i j = ((G i j).re : ℂ))
    (hNonneg : ∀ i j, 0 ≤ (G i j).re)
    (hSum : ∀ i, ∑ j, (G i j).re = c) :
    (c • (1 : Mat ι) - G).PosSemidef := by
  have hHerm : (c • (1 : Mat ι) - G).IsHermitian := by
    rw [Matrix.IsHermitian]
    simp [Matrix.conjTranspose_sub, hG.eq]
  apply hermitian_diagonal_dominant_posSemidef _ hHerm
  intro i
  calc
    (∑ j ∈ Finset.univ.erase i, ‖(c • (1 : Mat ι) - G) i j‖) =
        ∑ j ∈ Finset.univ.erase i, (G i j).re := by
      apply Finset.sum_congr rfl
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero,
        zero_sub, norm_neg]
      rw [hReal i j]
      simp [abs_of_nonneg (hNonneg i j)]
    _ = c - (G i i).re := by rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hSum]
    _ ≤ ((c • (1 : Mat ι) - G) i i).re := by simp

/-- Transfer a rectangular Gram bound to the insertion operator itself. -/
theorem gram_bound_transfer {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) (c : ℝ) (hc : 0 < c)
    (hGram : (c • (1 : Mat κ) - A.conjTranspose * A).PosSemidef) :
    (c • (1 : Mat ι) - A * A.conjTranspose).PosSemidef := by
  let F : Mat ι := c • 1 - A * A.conjTranspose
  have hF : F.conjTranspose = F := by
    simp [F, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hid : c • F = F.conjTranspose * F +
      A * (c • (1 : Mat κ) - A.conjTranspose * A) * A.conjTranspose := by
    rw [hF]
    dsimp [F]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul, Matrix.mul_assoc]
    abel
  have hp := (Matrix.posSemidef_conjTranspose_mul_self F).add
    (hGram.mul_mul_conjTranspose_same A)
  rw [← hid] at hp
  have hh := hp.smul (le_of_lt (one_div_pos.mpr hc))
  simpa only [smul_smul, one_div_mul_cancel (ne_of_gt hc), one_smul] using hh

/-- Positive matrices have nonnegative trace pairing. -/
theorem positive_trace_pairing {ι : Type} [Fintype ι] [DecidableEq ι]
    (H ρ : Mat ι) (hH : H.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ (Matrix.trace (H * ρ)).re := by
  let B := CFC.sqrt ρ
  have hB : B.conjTranspose = B := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
  have hBB : B * B = ρ := by simpa only [pow_two] using CFC.sq_sqrt ρ
  have hh := (hH.mul_mul_conjTranspose_same B).trace_nonneg
  rw [hB, Matrix.trace_mul_cycle, hBB] at hh
  rw [Matrix.trace_mul_comm] at hh
  exact (RCLike.nonneg_iff.mp hh).1

end QuantumScope
