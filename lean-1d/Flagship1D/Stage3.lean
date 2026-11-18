import Flagship1D.Stage2

/-!
# Proofs for Lemma 4.6 of the classical construction (Douglas and Mghirbi, version 2.0.0): overlap degree, exponent bookkeeping, nested-test sum (raw flags)
-/

namespace Flagship1D

open MeasureTheory ProbabilityTheory

/-! ### The leaf overlap degree by an area count -/

theorem card_Ico_sub_add (c : ℤ) (A B : ℕ) :
    (Finset.Ico (c - (A : ℤ)) (c + (B : ℤ))).card = A + B := by
  rw [Int.card_Ico]; omega

theorem leafOverlapDegree : LeafOverlapDegree := by
  intro ι S S' ax ay corner fam hS hS' hdisj ℓ hℓ
  classical
  let enl : ι → Set (ℤ × ℤ) := fun x =>
    box ((corner x).1 - ((ax * S : ℕ) : ℤ)) ((corner x).2 - ((ay * S' : ℕ) : ℤ))
      ((2 + 2 * ax) * S) ((2 + 2 * ay) * S')
  let conf : Finset ι := fam.filter (fun ℓ' => ℓ' ≠ ℓ ∧ ¬ Disjoint (enl ℓ) (enl ℓ'))
  refine ⟨conf, ?_, fun ℓ' hℓ' hne hnd => Finset.mem_filter.mpr ⟨hℓ', hne, hnd⟩⟩
  let pts : ι → Finset (ℤ × ℤ) := fun x =>
    Finset.Ico (corner x).1 ((corner x).1 + ((2 * S : ℕ) : ℤ)) ×ˢ
      Finset.Ico (corner x).2 ((corner x).2 + ((2 * S' : ℕ) : ℤ))
  have hpts : ∀ x z, z ∈ pts x ↔ z ∈ box (corner x).1 (corner x).2 (2 * S) (2 * S') := by
    intro x z
    simp only [pts, Finset.mem_product, Finset.mem_Ico, mem_box]
    tauto
  let Kc : Finset (ℤ × ℤ) :=
    Finset.Ico ((corner ℓ).1 - (((2 + 2 * ax) * S : ℕ) : ℤ)) ((corner ℓ).1 + (((4 + 2 * ax) * S : ℕ) : ℤ)) ×ˢ
      Finset.Ico ((corner ℓ).2 - (((2 + 2 * ay) * S' : ℕ) : ℤ)) ((corner ℓ).2 + (((4 + 2 * ay) * S' : ℕ) : ℤ))
  let G : Finset ι := insert ℓ conf
  have hGfam : ∀ x ∈ G, x ∈ fam := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hℓ
    · exact (Finset.mem_filter.mp hx).1
  have hsub : ∀ x ∈ G, pts x ⊆ Kc := by
    intro x hx z hz
    rw [hpts, mem_box] at hz
    simp only [Kc, Finset.mem_product, Finset.mem_Ico]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · push_cast at hz ⊢
      have h1 : (0 : ℤ) ≤ (ax : ℤ) * S := by positivity
      have h2 : (0 : ℤ) ≤ (ay : ℤ) * S' := by positivity
      have h3 : (0 : ℤ) ≤ (S : ℤ) := by positivity
      have h4 : (0 : ℤ) ≤ (S' : ℤ) := by positivity
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · have hnd := (Finset.mem_filter.mp hx).2.2
      obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.mp hnd
      simp only [enl, mem_box] at hy1 hy2
      push_cast at hz hy1 hy2 ⊢
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hpd : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → Disjoint (pts x) (pts y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro z hzx hzy
    rw [hpts] at hzx hzy
    exact Set.disjoint_left.mp (hdisj x (hGfam x hx) y (hGfam y hy) hne) hzx hzy
  have hcardpts : ∀ x, (pts x).card = (2 * S) * (2 * S') := by
    intro x
    simp only [pts, Finset.card_product]
    rw [Int.card_Ico, Int.card_Ico]
    have e1 : ((corner x).1 + ((2 * S : ℕ) : ℤ) - (corner x).1).toNat = 2 * S := by omega
    have e2 : ((corner x).2 + ((2 * S' : ℕ) : ℤ) - (corner x).2).toNat = 2 * S' := by omega
    rw [e1, e2]
  have hU : (G.biUnion pts).card = G.card * ((2 * S) * (2 * S')) := by
    rw [Finset.card_biUnion (fun x hx y hy hne => hpd x hx y hy hne)]
    rw [Finset.sum_congr rfl (fun x _ => hcardpts x), Finset.sum_const, smul_eq_mul]
  have hUK : (G.biUnion pts).card ≤ Kc.card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
    exact hsub x hx hzx
  have hKc : Kc.card = ((6 + 4 * ax) * S) * ((6 + 4 * ay) * S') := by
    simp only [Kc, Finset.card_product]
    rw [card_Ico_sub_add, card_Ico_sub_add]
    ring
  have hGcard : G.card = conf.card + 1 := by
    apply Finset.card_insert_of_notMem
    intro h
    exact (Finset.mem_filter.mp h).2.1 rfl
  have key : G.card * (4 * (S * S')) ≤ (4 * ((3 + 2 * ax) * (3 + 2 * ay))) * (S * S') := by
    have := hU ▸ hUK
    rw [hKc] at this
    calc G.card * (4 * (S * S')) = G.card * ((2 * S) * (2 * S')) := by ring
      _ ≤ ((6 + 4 * ax) * S) * ((6 + 4 * ay) * S') := this
      _ = (4 * ((3 + 2 * ax) * (3 + 2 * ay))) * (S * S') := by ring
  have hSS : 0 < S * S' := Nat.mul_pos (by omega) (by omega)
  have key2 : G.card * 4 ≤ 4 * ((3 + 2 * ax) * (3 + 2 * ay)) := by
    apply Nat.le_of_mul_le_mul_right _ hSS
    calc G.card * 4 * (S * S') = G.card * (4 * (S * S')) := by ring
      _ ≤ _ := key
  omega

/-! ### Exponent bookkeeping -/

theorem exponentBookkeeping : ExponentBookkeeping := by
  intro C K M d Δ D hC hK hMd p hp0 hp1 hsmall α hα0 hα n
  have hΔ : (0 : ℝ) < (Δ : ℝ) + 1 := by positivity
  have hγD : (D : ℝ) + 1 ≤ (M - 2 * d) / ((Δ : ℝ) + 1) := by
    rw [le_div_iff₀ hΔ]
    nlinarith
  have h1 : α ^ (1 / ((Δ : ℝ) + 1)) ≤ (K * p ^ (M - 2 * d)) ^ (1 / ((Δ : ℝ) + 1)) :=
    Real.rpow_le_rpow hα0 hα (by positivity)
  have h2 : (K * p ^ (M - 2 * d)) ^ (1 / ((Δ : ℝ) + 1)) =
      K ^ (1 / ((Δ : ℝ) + 1)) * p ^ ((M - 2 * d) / ((Δ : ℝ) + 1)) := by
    rw [Real.mul_rpow hK (Real.rpow_nonneg hp0.le _), ← Real.rpow_mul hp0.le]
    congr 2
    ring
  have h3 : p ^ ((M - 2 * d) / ((Δ : ℝ) + 1)) ≤ p ^ ((D : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_ge hp0 hp1 hγD
  have h4 : p ^ ((D : ℝ) + 1) = p ^ D * p := by
    rw [Real.rpow_add hp0, Real.rpow_natCast, Real.rpow_one]
  have hK0 : 0 ≤ K ^ (1 / ((Δ : ℝ) + 1)) := Real.rpow_nonneg hK _
  have hbase : C * α ^ (1 / ((Δ : ℝ) + 1)) ≤ p ^ D := by
    calc C * α ^ (1 / ((Δ : ℝ) + 1))
        ≤ C * (K ^ (1 / ((Δ : ℝ) + 1)) * p ^ ((M - 2 * d) / ((Δ : ℝ) + 1))) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hC
      _ ≤ C * (K ^ (1 / ((Δ : ℝ) + 1)) * p ^ ((D : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK0) hC
      _ = (C * K ^ (1 / ((Δ : ℝ) + 1)) * p) * p ^ D := by rw [h4]; ring
      _ ≤ 1 * p ^ D := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = p ^ D := one_mul _
  have hb0 : 0 ≤ C * α ^ (1 / ((Δ : ℝ) + 1)) := mul_nonneg hC (Real.rpow_nonneg hα0 _)
  calc (C * α ^ (1 / ((Δ : ℝ) + 1))) ^ (2 ^ n) ≤ (p ^ D) ^ (2 ^ n) :=
        pow_le_pow_left₀ hb0 hbase _
    _ = p ^ (D * 2 ^ n) := by rw [← pow_mul]

/-! ### The first conclusion for raw flags: the nested-test sum is below 1/4 -/

theorem nestedTestSumRaw : NestedTestSumRaw := by
  intro P T w mx my hP hT hw p hp u hu hpu hsmall hcut a b
  have hprob := (lemma_4_2_probability P T w hP hT hw p hp u hu hpu).2 hsmall
  have hD : (1 : ℝ) ≤ (Dpair P T : ℝ) := by exact_mod_cast Dpair_ge_one P T
  have hw1 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  set C0 : ℝ := (((mx * P + 1) * (my * T + 1) : ℕ) : ℝ) / (Dpair P T : ℝ) with hC0def
  have hC0 : 0 < C0 := by
    rw [hC0def]
    apply div_pos _ (by linarith)
    have : 1 ≤ (mx * P + 1) * (my * T + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  set r : ℝ := Real.sqrt u with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg u
  have hr2 : r ^ 2 = u := Real.sq_sqrt hu
  have hu16 : u ≤ 1 / 16 := by
    have h16 : (16 : ℝ) ≤ (4 * (Dpair P T : ℝ) * w ^ 2) ^ 2 := by
      have : (4 : ℝ) ≤ 4 * (Dpair P T : ℝ) * w ^ 2 := by nlinarith
      nlinarith
    calc u ≤ ((4 * (Dpair P T : ℝ) * w ^ 2) ^ 2)⁻¹ := hsmall
      _ ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h16
      _ = 1 / 16 := by norm_num
  have hr1 : r ≤ 1 / 2 := by nlinarith
  have hterm : ∀ j : ℕ, keyNoise p hp
      {ω | ¬ Sparse P T w j
        ({z | ω z = true} ∩ box (a j) (b j) (mx * P ^ (j + 1)) (my * T ^ (j + 1)))} ≤
      ENNReal.ofReal ((C0 * r) * r ^ j) := by
    intro j
    refine (hprob.2 mx my j (a j) (b j)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hC0def]
    have e : u ^ ((1 / 2 : ℝ) * 2 ^ j) = r ^ (2 ^ j) := by
      rw [hrdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast (u ^ (1 / 2 : ℝ)) (2 ^ j),
        ← Real.rpow_mul hu]
      congr 1
      push_cast
      ring
    rw [e, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hC0.le
    rw [← pow_succ']
    exact pow_le_pow_of_le_one hr0 (by linarith) Nat.lt_two_pow_self
  have hsum : Summable (fun j : ℕ => (C0 * r) * r ^ j) :=
    (summable_geometric_of_lt_one hr0 (by linarith)).mul_left _
  have h8 : 8 * C0 * r < 1 := by
    have hsq : (8 * C0 * r) ^ 2 < 1 ^ 2 := by
      have : (8 * C0 * r) ^ 2 = 64 * C0 ^ 2 * u := by rw [← hr2]; ring
      rw [this, one_pow]
      have hpos : 0 < 64 * C0 ^ 2 := by positivity
      have := mul_lt_mul_of_pos_left hcut hpos
      rwa [mul_inv_cancel₀ hpos.ne'] at this
    exact lt_of_pow_lt_pow_left₀ 2 zero_le_one hsq
  calc ∑' j : ℕ, keyNoise p hp
        {ω | ¬ Sparse P T w j
          ({z | ω z = true} ∩ box (a j) (b j) (mx * P ^ (j + 1)) (my * T ^ (j + 1)))}
      ≤ ∑' j : ℕ, ENNReal.ofReal ((C0 * r) * r ^ j) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, (C0 * r) * r ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum).symm
    _ = ENNReal.ofReal ((C0 * r) * (1 - r)⁻¹) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
    _ < ENNReal.ofReal (1 / 4) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
        have h1r : 0 < 1 - r := by linarith
        rw [← div_eq_mul_inv, div_lt_iff₀ h1r]
        nlinarith

end Flagship1D
