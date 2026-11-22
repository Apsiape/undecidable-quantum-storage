import Flagship1D.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Proofs of Lemma 12.2 and of the arithmetic of Lemma 16.1 (quantum storage paper)
-/

namespace Flagship1D

open Finset

/-! ### A geometric tail bound -/

/-- If `f ≥ 0` at least halves from index `m` on, then `f` is summable and
`Σ f ≤ Σ_{n<m} f n + 2 f m` (the comparison test of Lemma 12.2's proof). -/
theorem summable_tsum_le_of_halving (f : ℕ → ℝ) (m : ℕ) (h0 : ∀ n, 0 ≤ f n)
    (hhalf : ∀ n, m ≤ n → f (n + 1) ≤ f n / 2) :
    Summable f ∧ ∑' n, f n ≤ (∑ n ∈ range m, f n) + 2 * f m := by
  have hgeom : ∀ k, f (k + m) ≤ f m * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_zero, mul_one]
    | succ k ih =>
      have h := hhalf (k + m) (by omega)
      rw [show k + 1 + m = k + m + 1 by omega, pow_succ]
      calc f (k + m + 1) ≤ f (k + m) / 2 := h
        _ ≤ f m * (1 / 2) ^ k / 2 := by linarith
        _ = f m * ((1 / 2) ^ k * (1 / 2)) := by ring
  have hg : Summable (fun k : ℕ => f m * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left (f m)
  have hs : Summable (fun k => f (k + m)) :=
    Summable.of_nonneg_of_le (fun k => h0 _) hgeom hg
  have hsf : Summable f := (summable_nat_add_iff m).mp hs
  refine ⟨hsf, ?_⟩
  have htail : ∑' k, f (k + m) ≤ f m * 2 := by
    calc ∑' k, f (k + m) ≤ ∑' k, f m * (1 / 2 : ℝ) ^ k := hs.tsum_le_tsum hgeom hg
      _ = f m * 2 := by rw [tsum_mul_left, tsum_geometric_two]
  rw [← hsf.sum_add_tsum_nat_add m]
  linarith

namespace Q1

/-! ### Positivity of the constants -/

theorem BR_pos (P T : ℕ) (hP : 1 ≤ P) : 1 ≤ BR P T := le_trans hP (le_max_left _ _)

theorem AR_pos {w s : ℕ} (hw : 1 ≤ w) (hs : 1 ≤ s) : 0 < AR w s := by
  unfold AR
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)) (by omega)

theorem NR_pos (P T : ℕ) : 0 < NR P T := by unfold NR; positivity

theorem DR_pos (P T : ℕ) : 0 < DR P T := by unfold DR Dpair; positivity

theorem JR_pos (w rx rt : ℕ) : 0 < JR w rx rt := by unfold JR; positivity

theorem tR_pos (P T d' j : ℕ) (hP : 1 ≤ P) : 0 < tR P T d' j := by
  unfold tR
  have hB : (0 : ℚ) < (BR P T : ℚ) := by
    have := BR_pos P T hP
    exact_mod_cast (by omega : 0 < BR P T)
  exact div_pos (pow_pos hB _) (pow_pos (by norm_num) _)

theorem SR_pos (P T d' : ℕ) (hP : 1 ≤ P) : 0 < SR P T d' := by
  unfold SR
  have h1 : 0 ≤ ∑ j ∈ Finset.Ico 1 (jStar P T d'), tR P T d' j :=
    Finset.sum_nonneg (fun j _ => (tR_pos P T d' j hP).le)
  have h2 := tR_pos P T d' (jStar P T d') hP
  linarith

theorem KR_pos (P T Nclk Cclk d' : ℕ) (hP : 1 ≤ P) (hN : 1 ≤ Nclk) :
    0 < KR P T Nclk Cclk d' := by
  unfold KR
  have h1 : (0 : ℚ) < (Nclk : ℚ) := by exact_mod_cast (by omega : 0 < Nclk)
  have h2 : (0 : ℚ) < (Cclk : ℚ) + 1 := by positivity
  exact mul_pos (mul_pos h1 (pow_pos h2 _)) (SR_pos P T d' hP)

theorem qR_nonneg (P T Nclk Cclk d' : ℕ) (δ : ℚ) : 0 ≤ qR P T Nclk Cclk d' δ := by
  unfold qR
  exact le_min (by norm_num) (sq_nonneg _)

theorem qR_pos (P T Nclk Cclk d' : ℕ) (δ : ℚ) (hP : 1 ≤ P) (hN : 1 ≤ Nclk) (hδ : 0 < δ) :
    0 < qR P T Nclk Cclk d' δ := by
  unfold qR
  exact lt_min (by norm_num) (pow_pos (div_pos hδ (KR_pos P T Nclk Cclk d' hP hN)) 2)

theorem eR0Q_pos (P T w s rx rt : ℕ) (hw : 1 ≤ w) (hs : 1 ≤ s) : 0 < eR0Q P T w s rx rt := by
  unfold eR0Q
  have hA : (0 : ℚ) < (AR w s : ℚ) := by exact_mod_cast AR_pos hw hs
  have hB : (0 : ℚ) < ((2 * NR P T * DR P T : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (by norm_num) (NR_pos P T)) (DR_pos P T)
  exact mul_pos (inv_pos.mpr hA) (zpow_pos hB _)

theorem eRcut_pos (P T w s rx rt Nclk Cclk d' : ℕ) (δ : ℚ) (hP : 1 ≤ P) (hw : 1 ≤ w)
    (hs : 1 ≤ s) (hN : 1 ≤ Nclk) (hδ : 0 < δ) : 0 < eRcut P T w s rx rt Nclk Cclk d' δ := by
  unfold eRcut
  have hA : (0 : ℚ) < (AR w s : ℚ) := by exact_mod_cast AR_pos hw hs
  have hND : (0 : ℚ) < (NR P T : ℚ) * (DR P T : ℚ) := by
    have h1 : (0 : ℚ) < (NR P T : ℚ) := by exact_mod_cast NR_pos P T
    have h2 : (0 : ℚ) < (DR P T : ℚ) := by exact_mod_cast DR_pos P T
    exact mul_pos h1 h2
  exact lt_min (eR0Q_pos P T w s rx rt hw hs)
    (mul_pos (inv_pos.mpr hA) (pow_pos (div_pos (qR_pos P T Nclk Cclk d' δ hP hN hδ) hND) _))

theorem eR0Q_cast (P T w s rx rt : ℕ) : ((eR0Q P T w s rx rt : ℚ) : ℝ) = eR0 P T w s rx rt := by
  simp [eR0Q, eR0]

theorem eRcut_le_eR0 (P T w s rx rt Nclk Cclk d' : ℕ) (δ : ℚ) :
    ((eRcut P T w s rx rt Nclk Cclk d' δ : ℚ) : ℝ) ≤ eR0 P T w s rx rt := by
  rw [← eR0Q_cast]
  have h : eRcut P T w s rx rt Nclk Cclk d' δ ≤ eR0Q P T w s rx rt := by
    unfold eRcut; exact min_le_left _ _
  exact_mod_cast h

/-! ### The rate bound `x = C_R e^{1/J_R} ≤ q_R` -/

theorem rate_le_qR (P T w s rx rt Nclk Cclk d' : ℕ) (δ : ℚ) (hw : 1 ≤ w) (hs : 1 ≤ s)
    (e : ℝ) (he0 : 0 ≤ e) (he : e ≤ (eRcut P T w s rx rt Nclk Cclk d' δ : ℝ)) :
    CR P T w s rx rt * e ^ cR w rx rt ≤ (qR P T Nclk Cclk d' δ : ℝ) := by
  have hA : (0 : ℝ) < (AR w s : ℝ) := by exact_mod_cast AR_pos hw hs
  have hN : (0 : ℝ) < (NR P T : ℝ) := by exact_mod_cast NR_pos P T
  have hD : (0 : ℝ) < (DR P T : ℝ) := by exact_mod_cast DR_pos P T
  have hN' : (NR P T : ℝ) ≠ 0 := hN.ne'
  have hD' : (DR P T : ℝ) ≠ 0 := hD.ne'
  have hJ : (JR w rx rt : ℕ) ≠ 0 := (JR_pos w rx rt).ne'
  have h1 : eRcut P T w s rx rt Nclk Cclk d' δ ≤
      (AR w s : ℚ)⁻¹ * (qR P T Nclk Cclk d' δ / ((NR P T : ℚ) * (DR P T : ℚ))) ^ (JR w rx rt) := by
    unfold eRcut; exact min_le_right _ _
  have h2 : (eRcut P T w s rx rt Nclk Cclk d' δ : ℝ) ≤
      (AR w s : ℝ)⁻¹ * ((qR P T Nclk Cclk d' δ : ℝ) / ((NR P T : ℝ) * (DR P T : ℝ))) ^
        (JR w rx rt) := by
    have h1' := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at h1'
    exact h1'
  have hq0 : (0 : ℝ) ≤ (qR P T Nclk Cclk d' δ : ℝ) := by
    exact_mod_cast qR_nonneg P T Nclk Cclk d' δ
  have hy0 : (0 : ℝ) ≤ (qR P T Nclk Cclk d' δ : ℝ) / ((NR P T : ℝ) * (DR P T : ℝ)) :=
    div_nonneg hq0 (mul_pos hN hD).le
  have hAe : (AR w s : ℝ) * e ≤
      ((qR P T Nclk Cclk d' δ : ℝ) / ((NR P T : ℝ) * (DR P T : ℝ))) ^ (JR w rx rt) := by
    have := mul_le_mul_of_nonneg_left (he.trans h2) hA.le
    rwa [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
  have hroot : ((AR w s : ℝ) * e) ^ cR w rx rt ≤
      (qR P T Nclk Cclk d' δ : ℝ) / ((NR P T : ℝ) * (DR P T : ℝ)) := by
    unfold cR
    rw [one_div]
    calc ((AR w s : ℝ) * e) ^ ((JR w rx rt : ℝ)⁻¹)
        ≤ (((qR P T Nclk Cclk d' δ : ℝ) / ((NR P T : ℝ) * (DR P T : ℝ))) ^ (JR w rx rt)) ^
            ((JR w rx rt : ℝ)⁻¹) :=
          Real.rpow_le_rpow (mul_nonneg hA.le he0) hAe (by positivity)
      _ = (qR P T Nclk Cclk d' δ : ℝ) / ((NR P T : ℝ) * (DR P T : ℝ)) :=
          Real.pow_rpow_inv_natCast hy0 hJ
  calc CR P T w s rx rt * e ^ cR w rx rt
      = (NR P T : ℝ) * (DR P T : ℝ) * ((AR w s : ℝ) * e) ^ cR w rx rt := by
        unfold CR cR; rw [Real.mul_rpow hA.le he0]; ring
    _ ≤ (NR P T : ℝ) * (DR P T : ℝ) *
          ((qR P T Nclk Cclk d' δ : ℝ) / ((NR P T : ℝ) * (DR P T : ℝ))) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (qR P T Nclk Cclk d' δ : ℝ) := by field_simp

/-! ### The doubly exponential terms -/

/-- `x^{2^{j-2}} ≤ √x 2^{-(2^{j-1}-1)}` for `0 ≤ x ≤ 1/4`, written for `j = n + 1`:
`√(x^{2^n}) ≤ √x (1/2)^{2^n - 1}`. -/
theorem sqrt_pow_two_pow_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (n : ℕ) :
    Real.sqrt (x ^ 2 ^ n) ≤ Real.sqrt x * (1 / 2) ^ (2 ^ n - 1) := by
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hyx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hyh : Real.sqrt x ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    calc x ≤ 1 / 4 := hx
      _ = (1 / 2) ^ 2 := by norm_num
  have h1 : x ^ 2 ^ n = (Real.sqrt x ^ 2 ^ n) ^ 2 := by
    calc x ^ 2 ^ n = (Real.sqrt x ^ 2) ^ 2 ^ n := by rw [hyx]
      _ = (Real.sqrt x ^ 2 ^ n) ^ 2 := by ring
  rw [h1, Real.sqrt_sq (pow_nonneg hy0 _)]
  have h3 : Real.sqrt x ^ 2 ^ n = Real.sqrt x * Real.sqrt x ^ (2 ^ n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]
  rw [h3]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg x) hyh _) hy0

/-- `(1 + r)^d ≤ (C+1)^{d'} B^{d' j}` for `0 ≤ r ≤ C B^j`, `B ≥ 1`, `0 ≤ d ≤ d'`. -/
theorem radius_factor_le (B C : ℝ) (hB : 1 ≤ B) (d' : ℕ) (d : ℝ)
    (hdd : d ≤ d') (j : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ C * B ^ j) :
    (1 + r) ^ d ≤ (C + 1) ^ d' * B ^ (d' * j) := by
  have h1 : (1 + r) ^ d ≤ (1 + r) ^ (d' : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hdd
  rw [Real.rpow_natCast] at h1
  have hBj : 1 ≤ B ^ j := one_le_pow₀ hB
  have h2 : 1 + r ≤ (C + 1) * B ^ j := by
    have : (C + 1) * B ^ j = C * B ^ j + B ^ j := by ring
    linarith
  calc (1 + r) ^ d ≤ (1 + r) ^ d' := h1
    _ ≤ ((C + 1) * B ^ j) ^ d' := pow_le_pow_left₀ (by linarith) h2 d'
    _ = (C + 1) ^ d' * B ^ (d' * j) := by rw [mul_pow, ← pow_mul, mul_comm j d']

theorem tR_cast (P T d' n : ℕ) :
    ((tR P T d' (n + 1) : ℚ) : ℝ) = (BR P T : ℝ) ^ (d' * (n + 1)) / 2 ^ (2 ^ n - 1) := by
  simp [tR]

/-- `B_R^{d'} ≤ 2^{2^n - 1}` once `n + 1 ≥ j_*`. -/
theorem BR_pow_le (P T d' n : ℕ) (hn : jStar P T d' ≤ n + 1) :
    BR P T ^ d' ≤ 2 ^ (2 ^ n - 1) := by
  unfold jStar at hn
  have hB : BR P T ≤ 2 ^ Nat.clog 2 (BR P T) := Nat.le_pow_clog (by norm_num) _
  have hn' : Nat.clog 2 (d' * Nat.clog 2 (BR P T) + 1) ≤ n := by omega
  have h2 : d' * Nat.clog 2 (BR P T) + 1 ≤ 2 ^ n :=
    (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) hn')
  calc BR P T ^ d' ≤ (2 ^ Nat.clog 2 (BR P T)) ^ d' := Nat.pow_le_pow_left hB d'
    _ = 2 ^ (Nat.clog 2 (BR P T) * d') := (pow_mul 2 _ d').symm
    _ ≤ 2 ^ (2 ^ n - 1) := by
        apply Nat.pow_le_pow_right (by norm_num)
        rw [mul_comm]
        exact Nat.le_sub_one_of_lt h2

/-- The ratio `t_{j+1}/t_j ≤ 1/2` for `j ≥ j_*` (here `j = n + 1`). -/
theorem tR_halving (P T d' n : ℕ) (hn : jStar P T d' ≤ n + 1) :
    ((tR P T d' (n + 1 + 1) : ℚ) : ℝ) ≤ ((tR P T d' (n + 1) : ℚ) : ℝ) / 2 := by
  rw [tR_cast, tR_cast]
  have hb : (BR P T : ℝ) ^ d' ≤ (2 : ℝ) ^ (2 ^ n - 1) := by
    exact_mod_cast BR_pow_le P T d' n hn
  have h1 : (2 : ℝ) ^ (2 ^ (n + 1) - 1) = 2 ^ 2 ^ n * 2 ^ (2 ^ n - 1) := by
    rw [← pow_add]
    congr 1
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega
  have h2 : (2 : ℝ) ^ 2 ^ n = 2 ^ (2 ^ n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  have h3 : (BR P T : ℝ) ^ (d' * (n + 1 + 1)) =
      (BR P T : ℝ) ^ (d' * (n + 1)) * (BR P T : ℝ) ^ d' := by
    ring
  rw [h1, h2, h3]
  have hZ : (0 : ℝ) < 2 ^ (2 ^ n - 1) := by positivity
  have hX : (0 : ℝ) ≤ (BR P T : ℝ) ^ (d' * (n + 1)) := by positivity
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hX) hZ.le]

/-- `Σ_{j ≥ 1} t_j ≤ S̄`, with summability. -/
theorem tR_summable_tsum_le (P T d' : ℕ) (hP : 1 ≤ P) :
    Summable (fun n : ℕ => ((tR P T d' (n + 1) : ℚ) : ℝ)) ∧
    ∑' n : ℕ, ((tR P T d' (n + 1) : ℚ) : ℝ) ≤ ((SR P T d' : ℚ) : ℝ) := by
  have hj : 1 ≤ jStar P T d' := by unfold jStar; omega
  obtain ⟨hs, hle⟩ := summable_tsum_le_of_halving (fun n => ((tR P T d' (n + 1) : ℚ) : ℝ))
    (jStar P T d' - 1)
    (fun n => by exact_mod_cast (tR_pos P T d' (n + 1) hP).le)
    (fun n hn => tR_halving P T d' n (by omega))
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  unfold SR
  push_cast
  rw [Finset.sum_Ico_eq_sum_range, Nat.sub_add_cancel hj]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by rw [add_comm])

end Q1

/-! ### Lemma 12.2 -/

theorem q1_l1_1_uniform : Q1_L1_1_Uniform := by
  intro P T w s rx rt Nclk Cclk hP hT hw hs hN hC r hr d' δ hδ
  have hKpos := Q1.KR_pos P T Nclk Cclk d' hP hN
  refine ⟨Q1.eRcut_pos P T w s rx rt Nclk Cclk d' δ hP hw hs hN hδ,
    Q1.eRcut_le_eR0 P T w s rx rt Nclk Cclk d' δ, ?_⟩
  intro d hd0 hdd e he0 he
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Q1.CR P T w s rx rt * e ^ Q1.cR w rx rt := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact mul_nonneg (by unfold Q1.CR; positivity) (Real.rpow_nonneg he0 _)
  have hxq : x ≤ (Q1.qR P T Nclk Cclk d' δ : ℝ) := by
    rw [hx]; exact Q1.rate_le_qR P T w s rx rt Nclk Cclk d' δ hw hs e he0 he
  have hq14 : (Q1.qR P T Nclk Cclk d' δ : ℝ) ≤ 1 / 4 := by
    have : Q1.qR P T Nclk Cclk d' δ ≤ 1 / 4 := by unfold Q1.qR; exact min_le_left _ _
    have h' := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at h'
    exact h'
  have hqK : (Q1.qR P T Nclk Cclk d' δ : ℝ) ≤
      ((δ : ℝ) / (Q1.KR P T Nclk Cclk d' : ℝ)) ^ 2 := by
    have : Q1.qR P T Nclk Cclk d' δ ≤ (δ / Q1.KR P T Nclk Cclk d') ^ 2 := by
      unfold Q1.qR; exact min_le_right _ _
    have h' := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at h'
    exact h'
  have hK : (0 : ℝ) < (Q1.KR P T Nclk Cclk d' : ℝ) := by exact_mod_cast hKpos
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hy : Real.sqrt x ≤ (δ : ℝ) / (Q1.KR P T Nclk Cclk d' : ℝ) := by
    rw [Real.sqrt_le_left (div_pos hδR hK).le]
    exact hxq.trans hqK
  have hzR : ∀ n : ℕ, Q1.zR P T w s rx rt (n + 1) e = x ^ 2 ^ n := by
    intro n; unfold Q1.zR; rw [Nat.add_sub_cancel, hx]
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = (Nclk : ℝ) * ((Cclk : ℝ) + 1) ^ d' := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  have hB1 : (1 : ℝ) ≤ (Q1.BR P T : ℝ) := by exact_mod_cast Q1.BR_pos P T hP
  have hterm : ∀ n : ℕ, (Nclk : ℝ) * (1 + r (n + 1)) ^ d *
      Real.sqrt (Q1.zR P T w s rx rt (n + 1) e) ≤
      K' * Real.sqrt x * ((Q1.tR P T d' (n + 1) : ℚ) : ℝ) := by
    intro n
    rw [hzR n, Q1.tR_cast]
    have h1 := Q1.radius_factor_le (Q1.BR P T : ℝ) (Cclk : ℝ) hB1 d' d hdd
      (n + 1) (r (n + 1)) (hr (n + 1) (by omega)).1 (hr (n + 1) (by omega)).2
    have h2 := Q1.sqrt_pow_two_pow_le x hx0 (hxq.trans hq14) n
    have hN0 : (0 : ℝ) ≤ (Nclk : ℝ) := by positivity
    calc (Nclk : ℝ) * (1 + r (n + 1)) ^ d * Real.sqrt (x ^ 2 ^ n)
        ≤ (Nclk : ℝ) * (((Cclk : ℝ) + 1) ^ d' * (Q1.BR P T : ℝ) ^ (d' * (n + 1))) *
            (Real.sqrt x * (1 / 2) ^ (2 ^ n - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hN0) h2 (Real.sqrt_nonneg _) (by positivity)
      _ = K' * Real.sqrt x * ((Q1.BR P T : ℝ) ^ (d' * (n + 1)) / 2 ^ (2 ^ n - 1)) := by
          rw [hK', one_div_pow]; ring
  obtain ⟨hts, htle⟩ := Q1.tR_summable_tsum_le P T d' hP
  have hg : Summable (fun n : ℕ => K' * Real.sqrt x * ((Q1.tR P T d' (n + 1) : ℚ) : ℝ)) :=
    hts.mul_left _
  have hnn : ∀ n : ℕ, 0 ≤ (Nclk : ℝ) * (1 + r (n + 1)) ^ d *
      Real.sqrt (Q1.zR P T w s rx rt (n + 1) e) := by
    intro n
    have : 0 ≤ 1 + r (n + 1) := by linarith [(hr (n + 1) (by omega)).1]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg this _)) (Real.sqrt_nonneg _)
  have hsum : Summable (fun n : ℕ => (Nclk : ℝ) * (1 + r (n + 1)) ^ d *
      Real.sqrt (Q1.zR P T w s rx rt (n + 1) e)) :=
    Summable.of_nonneg_of_le hnn hterm hg
  refine ⟨hsum, ?_⟩
  calc ∑' n : ℕ, (Nclk : ℝ) * (1 + r (n + 1)) ^ d * Real.sqrt (Q1.zR P T w s rx rt (n + 1) e)
      ≤ ∑' n : ℕ, K' * Real.sqrt x * ((Q1.tR P T d' (n + 1) : ℚ) : ℝ) :=
        hsum.tsum_le_tsum hterm hg
    _ = K' * Real.sqrt x * ∑' n : ℕ, ((Q1.tR P T d' (n + 1) : ℚ) : ℝ) := tsum_mul_left
    _ ≤ K' * Real.sqrt x * ((Q1.SR P T d' : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left htle (mul_nonneg hK'0 (Real.sqrt_nonneg _))
    _ = Real.sqrt x * (Q1.KR P T Nclk Cclk d' : ℝ) := by
        rw [hK']; unfold Q1.KR; push_cast; ring
    _ ≤ (δ : ℝ) / (Q1.KR P T Nclk Cclk d' : ℝ) * (Q1.KR P T Nclk Cclk d' : ℝ) :=
        mul_le_mul_of_nonneg_right hy hK.le
    _ = (δ : ℝ) := by field_simp

theorem q1_l1_1 : Q1_L1_1 := by
  intro P T w s rx rt Nclk Cclk hP hT hw hs hN hC r hr d δ hd0 hδ
  obtain ⟨h1, h2, h3⟩ :=
    q1_l1_1_uniform P T w s rx rt Nclk Cclk hP hT hw hs hN hC r hr ⌈d⌉₊ δ hδ
  exact ⟨h1, h2, fun e he0 he => h3 d hd0 (Nat.le_ceil d) e he0 he⟩

/-! ### Lemma 16.1: recursion, horizon, fidelity constant -/

theorem q1_l18_recursion : Q1_L18_Recursion := by
  intro A C δ q b hA hC hq0 hq hb hbA hCδ u hu0 hu0' hrec
  have hAb : A * b ≤ 1 / 4 := by
    have := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * A)).mp hbA
    linarith
  have hAb2 : A * b ^ 2 ≤ b / 4 := by nlinarith
  have hCδ0 : 0 ≤ C * δ := le_trans (hu0 0) hu0'
  have key : ∀ i, u i ≤ b * (1 / 2) ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, mul_one]; linarith
    | succ i ih =>
      have hv0 : (0 : ℝ) ≤ (1 / 2) ^ i := by positivity
      have hv1 : ((1 : ℝ) / 2) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hui : u i ^ 2 ≤ (b * (1 / 2) ^ i) ^ 2 := pow_le_pow_left₀ (hu0 i) ih 2
      have h14 : (((1 : ℝ) / 2) ^ i) ^ 2 = (1 / 4) ^ i := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have hqi : q ^ i ≤ (((1 : ℝ) / 2) ^ i) ^ 2 := by
        rw [h14]; exact pow_le_pow_left₀ hq0 hq i
      calc u (i + 1) ≤ A * u i ^ 2 + C * δ * q ^ i := hrec i
        _ ≤ A * (b * (1 / 2) ^ i) ^ 2 + C * δ * ((1 / 2) ^ i) ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hui (by linarith))
              (mul_le_mul_of_nonneg_left hqi hCδ0)
        _ = (A * b ^ 2 + C * δ) * ((1 / 2) ^ i) ^ 2 := by ring
        _ ≤ (b / 2) * ((1 / 2) ^ i) ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (b / 2) * (1 / 2) ^ i := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
        _ = b * (1 / 2) ^ (i + 1) := by rw [pow_succ]; ring
  intro i
  have := key i
  rwa [one_div_pow, mul_one_div] at this

theorem q1_l18_horizon : Q1_L18_Horizon := by
  intro Ccone P T L k hP hPT hk
  have hmax : L < 4 * Ccone * (T ^ (k + 1) + P ^ (k + 1) + 1) := by
    by_contra h
    push Not at h
    have := hk.2 (show k + 1 ∈ {k' : ℕ | 4 * Ccone * (T ^ k' + P ^ k' + 1) ≤ L} from h)
    omega
  have h1 : P ^ (k + 1) ≤ T ^ (k + 1) := Nat.pow_le_pow_left hPT _
  have h2 : 1 ≤ T ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hL : L < 12 * Ccone * T * T ^ k := by
    calc L < 4 * Ccone * (T ^ (k + 1) + P ^ (k + 1) + 1) := hmax
      _ ≤ 4 * Ccone * (3 * T ^ (k + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 12 * Ccone * T * T ^ k := by ring
  refine ⟨hL, fun k0 hk0 => hk.2 hk0, fun Dlayer hD => ?_⟩
  have hCpos : 0 < Ccone := by
    rcases Nat.eq_zero_or_pos Ccone with h | h
    · subst h; simp at hL
    · exact h
  have hC' : (0 : ℝ) < (Ccone : ℝ) := by exact_mod_cast hCpos
  have hT' : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hc : (0 : ℝ) < 12 * (Ccone : ℝ) * (T : ℝ) := mul_pos (mul_pos (by norm_num) hC') hT'
  have hLR : (L : ℝ) < 12 * (Ccone : ℝ) * (T : ℝ) * ((T ^ k : ℕ) : ℝ) := by exact_mod_cast hL
  have hlt : 1 / (12 * (Ccone : ℝ) * (T : ℝ)) * (L : ℝ) < ((T ^ k : ℕ) : ℝ) := by
    rw [one_div_mul_eq_div, div_lt_iff₀ hc]; linarith
  refine ⟨hlt, Nat.le_mul_of_pos_left _ hD, fun t ht => ?_⟩
  have h3 : (t : ℝ) ≤ 1 / (12 * (Ccone : ℝ) * (T : ℝ)) * (L : ℝ) :=
    (Nat.cast_le.mpr ht).trans (Nat.floor_le (by positivity))
  have h4 : t < T ^ k := by exact_mod_cast h3.trans_lt hlt
  calc t ≤ T ^ k := h4.le
    _ ≤ Dlayer * T ^ k := Nat.le_mul_of_pos_left _ hD

theorem q1_l18_fidelity : Q1_L18_Fidelity := by
  intro A C δ q b hA hC hq0 hq hb hbA hCδ u hu0 hu0' hrec Ctop k0 k m hk0 htop hkk hm
    F pHelp pTop p hHelp hp hTop hF
  have huk : u k ≤ b / 2 ^ k :=
    q1_l18_recursion A C δ q b hA hC hq0 hq hb hbA hCδ u hu0 hu0' hrec k
  have hsum : ∑ i, p i ≤ (m : ℝ) * (b / 2 ^ k) := by
    calc ∑ i, p i ≤ ∑ _i : Fin m, b / 2 ^ k :=
          Finset.sum_le_sum (fun i _ => (hp i).trans huk)
      _ = (m : ℝ) * (b / 2 ^ k) := by simp
  have hbk : (0 : ℝ) ≤ b / 2 ^ k := div_nonneg hb.le (by positivity)
  have hmC : (m : ℝ) * (b / 2 ^ k) ≤ (Ctop : ℝ) * b / 2 ^ k0 := by
    have h1 : (m : ℝ) ≤ Ctop := by exact_mod_cast hm
    have h2 : b / 2 ^ k ≤ b / 2 ^ k0 :=
      div_le_div_of_nonneg_left hb.le (by positivity) (pow_le_pow_right₀ (by norm_num) hkk)
    calc (m : ℝ) * (b / 2 ^ k) ≤ (Ctop : ℝ) * (b / 2 ^ k0) :=
          mul_le_mul h1 h2 hbk (by positivity)
      _ = (Ctop : ℝ) * b / 2 ^ k0 := by ring
  have h5 : (m : ℝ) * (b / 2 ^ k) ≤ (Ctop : ℝ) * b / 2 ^ k := by
    have h1 : (m : ℝ) ≤ Ctop := by exact_mod_cast hm
    calc (m : ℝ) * (b / 2 ^ k) ≤ (Ctop : ℝ) * (b / 2 ^ k) := mul_le_mul_of_nonneg_right h1 hbk
      _ = (Ctop : ℝ) * b / 2 ^ k := by ring
  refine ⟨by linarith, by linarith, by linarith, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem q1_l18_k0 : Q1_L18_K0 := by
  refine ⟨fun Ctop b => ?_, fun Ctop b hb => ⟨by omega, ?_⟩⟩
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (32 * ((Ctop : ℝ) * b)) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n + 1, by omega, ?_⟩
    rw [div_le_iff₀ (by positivity), pow_succ]
    have : (0 : ℝ) < 2 ^ n := by positivity
    linarith
  · have hC : (Ctop : ℝ) ≤ 2 ^ Nat.clog 2 Ctop := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) Ctop
    have hX : (0 : ℝ) < 2 ^ Nat.clog 2 Ctop := by positivity
    have hR : (0 : ℝ) ≤ 1 / 32 * (2 ^ Nat.clog 2 Ctop * 2 ^ 3) := by positivity
    rw [div_le_iff₀ (by positivity), pow_add]
    rcases le_or_gt b 0 with h | h
    · have : (Ctop : ℝ) * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      linarith
    · nlinarith [mul_le_mul_of_nonneg_right hC h.le, mul_le_mul_of_nonneg_left hb hX.le]

theorem q1_l18_rank_exists : Q1_L18_RankExists := by
  intro Ccone P T L k0 hC hP hPT hk0
  have hbdd : BddAbove {k' : ℕ | 4 * Ccone * (T ^ k' + P ^ k' + 1) ≤ L} := by
    refine ⟨L, ?_⟩
    rw [mem_upperBounds]
    intro a ha
    have ha' : 4 * Ccone * (T ^ a + P ^ a + 1) ≤ L := ha
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : 2 ^ a ≤ T ^ a := Nat.pow_le_pow_left (by omega) a
    have h3 : T ^ a ≤ 4 * Ccone * (T ^ a + P ^ a + 1) :=
      ((Nat.le_add_right (T ^ a) (P ^ a)).trans (Nat.le_add_right _ 1)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hne : ({k' : ℕ | 4 * Ccone * (T ^ k' + P ^ k' + 1) ≤ L} : Set ℕ).Nonempty := ⟨k0, hk0⟩
  exact ⟨sSup {k' : ℕ | 4 * Ccone * (T ^ k' + P ^ k' + 1) ≤ L},
    ⟨Nat.sSup_mem hne hbdd, by rw [mem_upperBounds]; exact fun a ha => le_csSup hbdd ha⟩,
    le_csSup hbdd hk0⟩

theorem q1_l18_fidelity_at_times : Q1_L18_FidelityAtTimes := by
  intro A C δ q b hA hC hq0 hq hb hbA hCδ u hu0 hu0' hrec Ccone P T L k Dlayer Ctop k0 m hP hPT hk
    hD hk0 htop hkk hm F pHelp pTop p hacc t ht
  obtain ⟨-, -, hH⟩ := q1_l18_horizon Ccone P T L k hP hPT hk
  obtain ⟨-, -, htime⟩ := hH Dlayer hD
  obtain ⟨h1, h2, h3, h4⟩ := hacc t (htime t ht)
  have hF := q1_l18_fidelity A C δ q b hA hC hq0 hq hb hbA hCδ u hu0 hu0' hrec Ctop k0 k m hk0 htop
    hkk hm (F t) (pHelp t) (pTop t) (p t) h1 h2 h3 h4
  exact ⟨hF.2.2.1, hF.2.1⟩

/-! ### Lemmas 14.1 and 14.2: the exponent ledger -/

theorem q1_l12_ledger : Q1_L12_Ledger := by
  refine ⟨fun R d => ?_, by unfold Sel.Δad; norm_num, fun i => Nat.lt_two_pow_self (n := i), fun j hj => ?_⟩
  swap
  · have := Nat.lt_two_pow_self (n := j - 1)
    omega
  have hMs1 : 2 * Sel.ρs R + 2 * (Sel.Δad + 1) * Sel.Ds R d + 20 ≤ Sel.Ms R d := le_max_left _ _
  have hMs2 : 2 * (d + 1) * Sel.ρs R + 20 ≤ Sel.Ms R d := le_max_right _ _
  have hMl1 : 2 * Sel.ρl R d + 2 * (Sel.Δad + 1) * Sel.Dl R d + 20 ≤ Sel.Ml R d := le_max_left _ _
  have hMl2 : 2 * (d + 1) * Sel.ρl R d + 20 ≤ Sel.Ml R d := le_max_right _ _
  have hb : 21 ≤ Sel.bRefresh R d := le_max_left _ _
  have hDs : Sel.Ds R d = 2 * (d * Sel.ρs R) + 20 := by unfold Sel.Ds; ring
  have hDl : Sel.Dl R d = 2 * (d * Sel.ρl R d) + 20 := by unfold Sel.Dl; ring
  have hMs2' : ((2 * (d + 1) * Sel.ρs R + 20 : ℕ) : ℚ) ≤ (Sel.Ms R d : ℚ) := by exact_mod_cast hMs2
  have hMl2' : ((2 * (d + 1) * Sel.ρl R d + 20 : ℕ) : ℚ) ≤ (Sel.Ml R d : ℚ) := by exact_mod_cast hMl2
  push_cast at hMs2' hMl2'
  have hρs : (0 : ℚ) ≤ Sel.ρs R := by positivity
  have hρl : (0 : ℚ) ≤ Sel.ρl R d := by positivity
  refine ⟨?_, ?_, by omega, ?_, ?_, by linarith, by linarith, by linarith, by linarith,
    by rw [hDs]; omega, by rw [hDl]; omega⟩
  · unfold Sel.hRed; push_cast; ring
  · unfold Sel.CPref; omega
  · have h : ((2 * Sel.ρs R + 2 * (Sel.Δad + 1) * Sel.Ds R d + 20 : ℕ) : ℤ) ≤ (Sel.Ms R d : ℤ) := by
      exact_mod_cast hMs1
    push_cast at h; linarith
  · have h : ((2 * Sel.ρl R d + 2 * (Sel.Δad + 1) * Sel.Dl R d + 20 : ℕ) : ℤ) ≤ (Sel.Ml R d : ℤ) := by
      exact_mod_cast hMl1
    push_cast at h; linarith

theorem q1_l12_step1 : Q1_L12_Step1 := by
  intro R d p CN ζ hp hCN
  have hp0 : p ≠ 0 := hp.ne'
  have hpC : p ^ (-(Sel.CPref R d : ℤ)) = (p ^ Sel.CPref R d)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hpos : 0 < p ^ Sel.CPref R d := pow_pos hp _
  rw [hpC]
  refine ⟨?_, fun hζ => ?_, fun C' hC' h4 => ?_⟩
  · have h1 : Sel.hRed R d + 1 = Sel.CPref R d + (Sel.Ml R d + 6) := by unfold Sel.hRed; omega
    rw [h1, pow_add, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  · have h2 : Sel.Ml R d + Sel.CPref R d + 2 = Sel.CPref R d + (Sel.Ml R d + 2) := by omega
    have hc : 0 ≤ 2 * CN * (p ^ Sel.CPref R d)⁻¹ :=
      mul_nonneg (mul_nonneg (by norm_num) hCN.le) (inv_nonneg.mpr hpos.le)
    calc 2 * CN * (p ^ Sel.CPref R d)⁻¹ * ζ
        ≤ 2 * CN * (p ^ Sel.CPref R d)⁻¹ * (p ^ (Sel.Ml R d + Sel.CPref R d + 2) / (16 * CN)) :=
          mul_le_mul_of_nonneg_left hζ hc
      _ = p ^ (Sel.Ml R d + 2) / 8 := by
          rw [h2, pow_add]
          field_simp
          ring
  · have hM : (0 : ℝ) ≤ p ^ (Sel.Ml R d + 2) := by positivity
    have h8 : p ^ 4 * (8 * C') ≤ 1 := (le_div_iff₀ (by linarith)).mp h4
    have hsplit : p ^ (Sel.Ml R d + 6) = p ^ 4 * p ^ (Sel.Ml R d + 2) := by ring
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right h8 hM]

theorem q1_l11_ledger : Q1_L11_Ledger := by
  refine ⟨fun R d => ⟨?_, ?_, ?_, ?_⟩, fun m nbin => ⟨?_, ?_⟩, fun n J => ⟨?_, ?_⟩,
    fun R d => ⟨⟨2 * Sel.Ms R d + 42, by unfold Sel.sRead; omega⟩,
      ⟨10 * (Sel.Ml R d + 20), by unfold Sel.mCh; omega⟩, ⟨Sel.vRep R d - 1, ?_⟩⟩⟩
  · unfold Sel.sRead; push_cast; ring
  · have h : Sel.Ms R d + 20 ≤ Sel.bRefresh R d := le_max_right _ _
    omega
  · unfold Sel.vRep; push_cast; ring
  · unfold Sel.mCh; push_cast; ring
  · rw [div_lt_one (by positivity)]
    have : (0 : ℚ) ≤ m := by positivity
    linarith
  · have hX : (0 : ℚ) < 8 ^ (m + nbin) := by positivity
    rw [div_lt_div_iff₀ (by positivity) hX, show m + 1 + nbin = (m + nbin) + 1 by omega, pow_succ]
    have : (0 : ℚ) ≤ m := by positivity
    nlinarith
  · exact Nat.le_mul_of_pos_left _ (by positivity)
  · rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by omega), add_zero]
  · have : 20 ≤ Sel.vRep R d := by unfold Sel.vRep; omega
    omega

/-! ### Satisfiability of the hypothesis bundles -/

theorem q1_l1_1_satisfiable :
    ∃ (P T w s rx rt Nclk Cclk : ℕ) (r : ℕ → ℝ) (d : ℝ) (δ : ℚ),
      1 ≤ P ∧ 1 ≤ T ∧ 1 ≤ w ∧ 1 ≤ s ∧ 1 ≤ Nclk ∧ 1 ≤ Cclk ∧
      (∀ j, 1 ≤ j → 0 ≤ r j ∧ r j ≤ (Cclk : ℝ) * (Q1.BR P T : ℝ) ^ j) ∧ 0 ≤ d ∧ 0 < δ ∧
      0 < Q1.eRcut P T w s rx rt Nclk Cclk ⌈d⌉₊ δ :=
  ⟨1, 1, 1, 1, 0, 0, 1, 1, fun _ => 0, 0, 1, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    fun _ _ => ⟨le_rfl, by show (0 : ℝ) ≤ _; positivity⟩, le_rfl, one_pos,
    Q1.eRcut_pos 1 1 1 1 0 0 1 1 _ 1 le_rfl le_rfl le_rfl le_rfl one_pos⟩

theorem q1_l18_satisfiable :
    (∃ (A C δ q b : ℝ) (u : ℕ → ℝ), 1 ≤ A ∧ 1 ≤ C ∧ 0 ≤ q ∧ q ≤ 1 / 4 ∧ 0 < b ∧
      b ≤ 1 / (4 * A) ∧ C * δ ≤ b / 4 ∧ (∀ i, 0 ≤ u i) ∧ u 0 ≤ C * δ ∧
      (∀ i, u (i + 1) ≤ A * u i ^ 2 + C * δ * q ^ i)) ∧
    (∃ (Ccone P T L k : ℕ), 2 ≤ P ∧ P ≤ T ∧
      IsGreatest {k' : ℕ | 4 * Ccone * (T ^ k' + P ^ k' + 1) ≤ L} k) ∧
    (∃ (Ctop k0 k m : ℕ) (F pHelp pTop : ℝ) (p : Fin m → ℝ),
      1 ≤ k0 ∧ (Ctop : ℝ) * (1 / 4) / 2 ^ k0 ≤ 1 / 32 ∧ k0 ≤ k ∧ m ≤ Ctop ∧
      pHelp < 1 / 128 ∧ (∀ i, p i ≤ 0) ∧ pTop ≤ ∑ i, p i ∧ 1 - pHelp - pTop ≤ F) := by
  refine ⟨⟨1, 1, 0, 0, 1 / 4, fun _ => 0, ?_⟩, ⟨1, 2, 2, 12, 0, le_rfl, le_rfl, ?_, ?_⟩,
    ⟨0, 1, 1, 0, 1, 0, 0, fun _ => 0, ?_⟩⟩
  · refine ⟨le_rfl, le_rfl, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      fun _ => le_rfl, by norm_num, fun i => ?_⟩
    simp
  · show 4 * 1 * (2 ^ 0 + 2 ^ 0 + 1) ≤ 12
    norm_num
  · rw [mem_upperBounds]
    intro a ha
    have ha' : 4 * 1 * (2 ^ a + 2 ^ a + 1) ≤ 12 := ha
    by_contra h
    have h2 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · refine ⟨le_rfl, by norm_num, le_rfl, le_rfl, by norm_num, fun _ => le_rfl, by simp,
      by norm_num⟩

theorem q1_l18_at_times_satisfiable :
    ∃ (A C δ q b : ℝ) (u : ℕ → ℝ) (Ccone P T L k Dlayer Ctop k0 m : ℕ)
      (F pHelp pTop : ℕ → ℝ) (p : ℕ → Fin m → ℝ),
      (1 ≤ A ∧ 1 ≤ C ∧ 0 ≤ q ∧ q ≤ 1 / 4 ∧ 0 < b ∧ b ≤ 1 / (4 * A) ∧ C * δ ≤ b / 4) ∧
      ((∀ i, 0 ≤ u i) ∧ u 0 ≤ C * δ ∧ (∀ i, u (i + 1) ≤ A * u i ^ 2 + C * δ * q ^ i)) ∧
      (2 ≤ P ∧ P ≤ T ∧ IsGreatest {k' : ℕ | 4 * Ccone * (T ^ k' + P ^ k' + 1) ≤ L} k ∧
        1 ≤ Dlayer) ∧
      (1 ≤ k0 ∧ (Ctop : ℝ) * b / 2 ^ k0 ≤ 1 / 32 ∧ k0 ≤ k ∧ m ≤ Ctop) ∧
      (∀ t : ℕ, t ≤ Dlayer * T ^ k → pHelp t < 1 / 128 ∧ (∀ i, p t i ≤ u k) ∧
        pTop t ≤ ∑ i, p t i ∧ 1 - pHelp t - pTop t ≤ F t) ∧
      1 ≤ ⌊1 / (12 * (Ccone : ℝ) * (T : ℝ)) * (L : ℝ)⌋₊ := by
  refine ⟨1, 1, 0, 0, 1 / 4, fun _ => 0, 1, 2, 2, 516, 6, 1, 8, 6, 8, fun _ => 1, fun _ => 0,
    fun _ => 0, fun _ _ => 0, ⟨le_rfl, le_rfl, le_rfl, by norm_num, by norm_num, by norm_num,
    by norm_num⟩, ⟨fun _ => le_rfl, by norm_num, fun i => by simp⟩,
    ⟨le_rfl, le_rfl, ⟨?_, ?_⟩, le_rfl⟩, ⟨by norm_num, by norm_num, le_rfl, le_rfl⟩, ?_, ?_⟩
  · show 4 * 1 * (2 ^ 6 + 2 ^ 6 + 1) ≤ 516
    norm_num
  · rw [mem_upperBounds]
    intro a ha
    have ha' : 4 * 1 * (2 ^ a + 2 ^ a + 1) ≤ 516 := ha
    by_contra h
    have h2 : 128 ≤ 2 ^ a := by
      calc 128 = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro t _
    exact ⟨by norm_num, fun _ => le_rfl, by simp, by norm_num⟩
  · exact Nat.le_floor (by norm_num)

end Flagship1D
