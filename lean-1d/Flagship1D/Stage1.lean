import Flagship1D.Defs

/-!
# Proofs: sparsity, Lemma 4.2, selection, independence, tree bound, parameters

Every theorem here has as its type one of the `Prop` statements of
`Flagship1D/Defs.lean`.
-/

namespace Flagship1D

open MeasureTheory ProbabilityTheory

/-! ## 1. Sparsity basics -/

theorem mem_box {a b : ℤ} {L M : ℕ} {z : ℤ × ℤ} :
    z ∈ box a b L M ↔ a ≤ z.1 ∧ z.1 < a + (L : ℤ) ∧ b ≤ z.2 ∧ z.2 < b + (M : ℤ) := Iff.rfl

theorem sparse_zero_iff {P T w : ℕ} {E : Set (ℤ × ℤ)} : Sparse P T w 0 E ↔ E = ∅ := Iff.rfl

theorem sparse_succ_iff {P T w j : ℕ} {E : Set (ℤ × ℤ)} :
    Sparse P T w (j + 1) E ↔ ∀ a b : ℤ, ∃ c d : ℤ,
      Sparse P T w j ((E ∩ box a b (w * P ^ (j + 1)) (w * T ^ (j + 1))) \
        box c d (3 * w * P ^ j) (3 * w * T ^ j)) := Iff.rfl

theorem sparse_empty (P T w : ℕ) : ∀ j, Sparse P T w j ∅
  | 0 => rfl
  | j + 1 => fun _ _ => ⟨0, 0, by simpa using sparse_empty P T w j⟩

theorem sparse_mono (P T w : ℕ) :
    ∀ (j : ℕ) {E F : Set (ℤ × ℤ)}, F ⊆ E → Sparse P T w j E → Sparse P T w j F
  | 0, E, F, hFE, hE => by
      rw [sparse_zero_iff] at hE ⊢
      subst hE
      exact Set.subset_empty_iff.mp hFE
  | j + 1, E, F, hFE, hE => by
      rw [sparse_succ_iff] at hE ⊢
      intro a b
      obtain ⟨c, d, h⟩ := hE a b
      exact ⟨c, d, sparse_mono P T w j
        (Set.sdiff_subset_sdiff_left (Set.inter_subset_inter_left _ hFE)) h⟩

theorem sparseInheritedBySubsets : SparseInheritedBySubsets :=
  fun P T w j _ _ h hE => sparse_mono P T w j h hE

theorem sparseImpliesNextSparse : SparseImpliesNextSparse := by
  intro P T w j E hE
  rw [sparse_succ_iff]
  intro a b
  exact ⟨0, 0, sparse_mono P T w j (fun z hz => hz.1.1) hE⟩

/-- A set is `j`-sparse as soon as its intersection with every translate of `wV^j`
is contained in some `j`-sparse set. -/
theorem sparse_of_local (P T w : ℕ) (hw : 1 ≤ w) :
    ∀ (j : ℕ) (F : Set (ℤ × ℤ)),
      (∀ x y : ℤ, ∃ G, Sparse P T w j G ∧ F ∩ box x y (w * P ^ j) (w * T ^ j) ⊆ G) →
      Sparse P T w j F
  | 0, F, h => by
      rw [sparse_zero_iff]
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      obtain ⟨G, hG, hFG⟩ := h z.1 z.2
      rw [sparse_zero_iff] at hG
      have hzb : z ∈ box z.1 z.2 (w * P ^ 0) (w * T ^ 0) := by
        rw [mem_box]
        have : (1 : ℤ) ≤ w := by exact_mod_cast hw
        simp only [pow_zero, mul_one]
        omega
      have := hFG ⟨hz, hzb⟩
      rw [hG] at this
      exact this
  | j + 1, F, h => by
      rw [sparse_succ_iff]
      intro x y
      obtain ⟨G, hG, hFG⟩ := h x y
      rw [sparse_succ_iff] at hG
      obtain ⟨c, d, hcd⟩ := hG x y
      exact ⟨c, d, sparse_mono P T w j
        (Set.sdiff_subset_sdiff_left (Set.subset_inter hFG Set.inter_subset_right)) hcd⟩

/-! ## 2. Lemma 4.2 -/

/-- One-dimensional cover: the trace on the parent `[a, a + 2ns)` of any window
`[x, x + s)` lies in one of the `2n - 1` doubled cells `[a + ks, a + ks + 2s)`. -/
theorem cover1D (a x : ℤ) (s n : ℕ) (hs : 0 < s) (hn : 1 ≤ n) :
    ∃ k, k < 2 * n - 1 ∧ ∀ y : ℤ, a ≤ y → y < a + ((2 * n * s : ℕ) : ℤ) → x ≤ y →
      y < x + (s : ℤ) →
      a + ((k * s : ℕ) : ℤ) ≤ y ∧ y < a + ((k * s : ℕ) : ℤ) + ((2 * s : ℕ) : ℤ) := by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  set q := (x - a) / (s : ℤ) with hq
  have h1 : q * s ≤ x - a := Int.ediv_mul_le _ (ne_of_gt hs')
  have h2 : x - a < (q + 1) * s := Int.lt_ediv_add_one_mul_self _ hs'
  rcases lt_or_ge q 0 with hq0 | hq0
  · refine ⟨0, by omega, ?_⟩
    intro y hy1 hy2 hy3 hy4
    have h3 : (q + 1) * (s : ℤ) ≤ 0 := by nlinarith
    push_cast at hy2 ⊢
    constructor <;> nlinarith
  · rcases le_or_gt q (2 * n - 2) with hq1 | hq1
    · refine ⟨q.toNat, by omega, ?_⟩
      intro y hy1 hy2 hy3 hy4
      have hqt : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
      push_cast at hy2 ⊢
      rw [hqt]
      constructor <;> nlinarith
    · refine ⟨2 * n - 2, by omega, ?_⟩
      intro y hy1 hy2 hy3 hy4
      have hcast : ((2 * n - 2 : ℕ) : ℤ) = 2 * (n : ℤ) - 2 := by omega
      have h4 : (2 * (n : ℤ) - 1) * s ≤ q * s := by
        apply mul_le_mul_of_nonneg_right _ hs'.le
        omega
      push_cast at hy2 ⊢
      rw [hcast]
      constructor <;> nlinarith

/-- Two doubled cells that meet have indices at most one apart. -/
theorem idx_close (a y : ℤ) (s k k' : ℕ)
    (h1 : a + ((k * s : ℕ) : ℤ) ≤ y) (h2 : y < a + ((k' * s : ℕ) : ℤ) + ((2 * s : ℕ) : ℤ)) :
    k ≤ k' + 1 := by
  have h3 : ((k * s : ℕ) : ℤ) < (((k' + 2) * s : ℕ) : ℤ) := by
    push_cast at h1 h2 ⊢
    linarith
  have h4 : k * s < (k' + 2) * s := by exact_mod_cast h3
  have := Nat.lt_of_mul_lt_mul_right h4
  omega

theorem childBox_mem {P T w j : ℕ} {a b : ℤ} {kl : ℕ × ℕ} {z : ℤ × ℤ} :
    z ∈ childBox P T w j a b kl ↔
      a + ((kl.1 * (w * P ^ j) : ℕ) : ℤ) ≤ z.1 ∧
      z.1 < a + ((kl.1 * (w * P ^ j) : ℕ) : ℤ) + ((2 * (w * P ^ j) : ℕ) : ℤ) ∧
      b + ((kl.2 * (w * T ^ j) : ℕ) : ℤ) ≤ z.2 ∧
      z.2 < b + ((kl.2 * (w * T ^ j) : ℕ) : ℤ) + ((2 * (w * T ^ j) : ℕ) : ℤ) := by
  simp only [childBox, mem_box]
  have e1 : 2 * w * P ^ j = 2 * (w * P ^ j) := by ring
  have e2 : 2 * w * T ^ j = 2 * (w * T ^ j) := by ring
  rw [e1, e2]

/-- Core of Lemma 4.2 (contrapositive form): if the bad children pairwise meet, the
restriction to the parent is `(j+1)`-sparse. -/
theorem parent_sparse (P T w j : ℕ) (a b : ℤ) (E : Set (ℤ × ℤ))
    (hP : 1 ≤ P) (hT : 1 ≤ T) (hw : 1 ≤ w)
    (hpair : ∀ kl ∈ childIndex P T, ∀ kl' ∈ childIndex P T,
      ¬ Sparse P T w j (E ∩ childBox P T w j a b kl) →
      ¬ Sparse P T w j (E ∩ childBox P T w j a b kl') →
      ¬ Disjoint (childBox P T w j a b kl) (childBox P T w j a b kl')) :
    Sparse P T w (j + 1) (E ∩ box a b (2 * w * P ^ (j + 1)) (2 * w * T ^ (j + 1))) := by
  classical
  have hs : 0 < w * P ^ j := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have ht : 0 < w * T ^ j := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  set Bad := (childIndex P T).filter
    (fun kl => ¬ Sparse P T w j (E ∩ childBox P T w j a b kl)) with hBad
  -- One translate of `3wV^j` contains every bad child.
  obtain ⟨c, d, hJ⟩ : ∃ c d : ℤ, ∀ kl ∈ Bad,
      childBox P T w j a b kl ⊆ box c d (3 * w * P ^ j) (3 * w * T ^ j) := by
    rcases Bad.eq_empty_or_nonempty with hE | hne
    · exact ⟨0, 0, by simp [hE]⟩
    · obtain ⟨p0, hp0, hmin0⟩ := Bad.exists_min_image (fun kl => kl.1) hne
      obtain ⟨p1, hp1, hmin1⟩ := Bad.exists_min_image (fun kl => kl.2) hne
      refine ⟨a + ((p0.1 * (w * P ^ j) : ℕ) : ℤ), b + ((p1.2 * (w * T ^ j) : ℕ) : ℤ), ?_⟩
      intro kl hkl
      have hkl' := Finset.mem_filter.mp hkl
      have hp0' := Finset.mem_filter.mp hp0
      have hp1' := Finset.mem_filter.mp hp1
      have hk1 : kl.1 ≤ p0.1 + 1 := by
        obtain ⟨z, hz1, hz2⟩ :=
          Set.not_disjoint_iff.mp (hpair kl hkl'.1 p0 hp0'.1 hkl'.2 hp0'.2)
        rw [childBox_mem] at hz1 hz2
        exact idx_close a z.1 _ _ _ hz1.1 hz2.2.1
      have hk2 : kl.2 ≤ p1.2 + 1 := by
        obtain ⟨z, hz1, hz2⟩ :=
          Set.not_disjoint_iff.mp (hpair kl hkl'.1 p1 hp1'.1 hkl'.2 hp1'.2)
        rw [childBox_mem] at hz1 hz2
        exact idx_close b z.2 _ _ _ hz1.2.2.1 hz2.2.2.2
      have hm0 : p0.1 ≤ kl.1 := hmin0 kl hkl
      have hm1 : p1.2 ≤ kl.2 := hmin1 kl hkl
      have i1 : p0.1 * (w * P ^ j) ≤ kl.1 * (w * P ^ j) := Nat.mul_le_mul_right _ hm0
      have i2 : kl.1 * (w * P ^ j) ≤ (p0.1 + 1) * (w * P ^ j) := Nat.mul_le_mul_right _ hk1
      have i3 : p1.2 * (w * T ^ j) ≤ kl.2 * (w * T ^ j) := Nat.mul_le_mul_right _ hm1
      have i4 : kl.2 * (w * T ^ j) ≤ (p1.2 + 1) * (w * T ^ j) := Nat.mul_le_mul_right _ hk2
      intro z hz
      rw [childBox_mem] at hz
      rw [mem_box]
      have e3 : 3 * w * P ^ j = 3 * (w * P ^ j) := by ring
      have e4 : 3 * w * T ^ j = 3 * (w * T ^ j) := by ring
      rw [e3, e4]
      have j1 : ((p0.1 * (w * P ^ j) : ℕ) : ℤ) ≤ ((kl.1 * (w * P ^ j) : ℕ) : ℤ) := by
        exact_mod_cast i1
      have j2 : ((kl.1 * (w * P ^ j) : ℕ) : ℤ) ≤ (((p0.1 + 1) * (w * P ^ j) : ℕ) : ℤ) := by
        exact_mod_cast i2
      have j3 : ((p1.2 * (w * T ^ j) : ℕ) : ℤ) ≤ ((kl.2 * (w * T ^ j) : ℕ) : ℤ) := by
        exact_mod_cast i3
      have j4 : ((kl.2 * (w * T ^ j) : ℕ) : ℤ) ≤ (((p1.2 + 1) * (w * T ^ j) : ℕ) : ℤ) := by
        exact_mod_cast i4
      push_cast at hz j1 j2 j3 j4 ⊢
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  -- Every bad child lies in the exceptional rectangle; every moving test meets the
  -- parent inside one child.
  rw [sparse_succ_iff]
  intro x y
  refine ⟨c, d, ?_⟩
  apply sparse_of_local P T w hw j
  intro x' y'
  obtain ⟨k, hk, hk'⟩ := cover1D a x' (w * P ^ j) P hs hP
  obtain ⟨l, hl, hl'⟩ := cover1D b y' (w * T ^ j) T ht hT
  have hkl : (k, l) ∈ childIndex P T := by
    simp only [childIndex, Finset.mem_product, Finset.mem_range]
    exact ⟨hk, hl⟩
  have hsub : box a b (2 * w * P ^ (j + 1)) (2 * w * T ^ (j + 1)) ∩
      box x' y' (w * P ^ j) (w * T ^ j) ⊆ childBox P T w j a b (k, l) := by
    rintro z ⟨hz1, hz2⟩
    rw [mem_box] at hz1 hz2
    have e1 : 2 * w * P ^ (j + 1) = 2 * P * (w * P ^ j) := by ring
    have e2 : 2 * w * T ^ (j + 1) = 2 * T * (w * T ^ j) := by ring
    rw [e1, e2] at hz1
    obtain ⟨u1, u2⟩ := hk' z.1 hz1.1 hz1.2.1 hz2.1 hz2.2.1
    obtain ⟨u3, u4⟩ := hl' z.2 hz1.2.2.1 hz1.2.2.2 hz2.2.2.1 hz2.2.2.2
    rw [childBox_mem]
    exact ⟨u1, u2, u3, u4⟩
  by_cases hgood : Sparse P T w j (E ∩ childBox P T w j a b (k, l))
  · refine ⟨_, hgood, ?_⟩
    rintro z ⟨⟨⟨⟨hE, hpar⟩, _⟩, _⟩, hQ'⟩
    exact ⟨hE, hsub ⟨hpar, hQ'⟩⟩
  · refine ⟨∅, sparse_empty P T w j, ?_⟩
    rintro z ⟨⟨⟨⟨_, hpar⟩, _⟩, hnJ⟩, hQ'⟩
    exact hnJ (hJ (k, l) (Finset.mem_filter.mpr ⟨hkl, hgood⟩) (hsub ⟨hpar, hQ'⟩))

theorem box_eq_empty_left {a b : ℤ} {M : ℕ} : box a b 0 M = ∅ := by
  ext z
  simp only [mem_box, Set.mem_empty_iff_false, iff_false]
  intro h
  push_cast at h
  omega

theorem box_eq_empty_right {a b : ℤ} {L : ℕ} : box a b L 0 = ∅ := by
  ext z
  simp only [mem_box, Set.mem_empty_iff_false, iff_false]
  intro h
  push_cast at h
  omega

theorem lemma_4_2_witness : Lemma_4_2_Witness := by
  intro P T w j a b
  refine ⟨?_, ?_, ?_⟩
  · simp only [childIndex, Finset.card_product, Finset.card_range]
    exact Nat.mul_le_mul (by omega) (by omega)
  · intro kl hkl z hz
    simp only [childIndex, Finset.mem_product, Finset.mem_range] at hkl
    rw [childBox_mem] at hz
    rw [mem_box]
    have e1 : 2 * w * P ^ (j + 1) = 2 * P * (w * P ^ j) := by ring
    have e2 : 2 * w * T ^ (j + 1) = 2 * T * (w * T ^ j) := by ring
    rw [e1, e2]
    have i1 : kl.1 * (w * P ^ j) + 2 * (w * P ^ j) ≤ 2 * P * (w * P ^ j) := by
      rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have i2 : kl.2 * (w * T ^ j) + 2 * (w * T ^ j) ≤ 2 * T * (w * T ^ j) := by
      rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have j1 : ((kl.1 * (w * P ^ j) + 2 * (w * P ^ j) : ℕ) : ℤ) ≤ ((2 * P * (w * P ^ j) : ℕ) : ℤ) := by
      exact_mod_cast i1
    have j2 : ((kl.2 * (w * T ^ j) + 2 * (w * T ^ j) : ℕ) : ℤ) ≤ ((2 * T * (w * T ^ j) : ℕ) : ℤ) := by
      exact_mod_cast i2
    push_cast at hz j1 j2 ⊢
    have k1 : (0 : ℤ) ≤ (kl.1 : ℤ) * ((w : ℤ) * (P : ℤ) ^ j) := by positivity
    have k2 : (0 : ℤ) ≤ (kl.2 : ℤ) * ((w : ℤ) * (T : ℤ) ^ j) := by positivity
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro E hns
    by_contra hcon
    apply hns
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      simp only [mul_zero, zero_mul, box_eq_empty_left, Set.inter_empty]
      exact sparse_empty P T 0 (j + 1)
    rcases Nat.eq_zero_or_pos P with hP | hP
    · subst hP
      simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow,
        mul_zero, box_eq_empty_left, Set.inter_empty]
      exact sparse_empty 0 T w (j + 1)
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow,
        mul_zero, box_eq_empty_right, Set.inter_empty]
      exact sparse_empty P 0 w (j + 1)
    apply parent_sparse P T w j a b E hP hT hw
    intro kl hkl kl' hkl' h1 h2 hdisj
    exact hcon ⟨kl, hkl, kl', hkl', hdisj, h1, h2⟩

/-- A full `V^j` is never `j`-sparse (under `w ≥ 1`, `T ≥ 1`, `P ≥ 3w + 2`). -/
theorem fullBoxNotSparse : FullBoxNotSparse := by
  intro P T w hw hP hT j
  induction j with
  | zero =>
    intro a b h
    rw [sparse_zero_iff] at h
    have hab : (a, b) ∈ box a b (P ^ 0) (T ^ 0) := by
      rw [mem_box]; simp
    rw [h] at hab
    exact hab
  | succ j ih =>
    intro a b h
    rw [sparse_succ_iff] at h
    obtain ⟨c, d, hcd⟩ := h a b
    have hs0 : 0 < P ^ j := pow_pos (by omega) _
    have f1 : (3 * w + 2) * P ^ j ≤ P ^ (j + 1) := by
      rw [pow_succ, mul_comm (P ^ j) P]; exact Nat.mul_le_mul_right _ hP
    have f2 : P ^ (j + 1) ≤ w * P ^ (j + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have f3 : T ^ j ≤ T ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have f4 : T ^ (j + 1) ≤ w * T ^ (j + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have g1 : (((3 * w + 2) * P ^ j : ℕ) : ℤ) ≤ ((P ^ (j + 1) : ℕ) : ℤ) := by exact_mod_cast f1
    have g2 : ((P ^ (j + 1) : ℕ) : ℤ) ≤ ((w * P ^ (j + 1) : ℕ) : ℤ) := by exact_mod_cast f2
    have g3 : ((T ^ j : ℕ) : ℤ) ≤ ((T ^ (j + 1) : ℕ) : ℤ) := by exact_mod_cast f3
    have g4 : ((T ^ (j + 1) : ℕ) : ℤ) ≤ ((w * T ^ (j + 1) : ℕ) : ℤ) := by exact_mod_cast f4
    have g5 : (0 : ℤ) ≤ ((w * P ^ j : ℕ) : ℤ) := by positivity
    have g6 : (0 : ℤ) < ((P ^ j : ℕ) : ℤ) := by exact_mod_cast hs0
    push_cast at g1 g2 g3 g4 g5 g6
    by_cases hc : a + ((P ^ j : ℕ) : ℤ) ≤ c
    · apply ih a b
      apply sparse_mono P T w j _ hcd
      intro z hz
      rw [mem_box] at hz
      push_cast at hz hc
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_box]; push_cast
        refine ⟨by linarith, by nlinarith, by linarith, by linarith⟩
      · rw [mem_box]; push_cast
        refine ⟨by linarith, by nlinarith, by linarith, by linarith⟩
      · rw [mem_box]; push_cast
        intro hJ
        linarith [hJ.1]
    · apply ih (a + (((3 * w + 1) * P ^ j : ℕ) : ℤ)) b
      apply sparse_mono P T w j _ hcd
      intro z hz
      rw [mem_box] at hz
      push_cast at hz hc
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_box]; push_cast
        refine ⟨by nlinarith, by nlinarith, by linarith, by linarith⟩
      · rw [mem_box]; push_cast
        refine ⟨by nlinarith, by nlinarith, by linarith, by linarith⟩
      · rw [mem_box]; push_cast
        intro hJ
        nlinarith [hJ.2.1]

/-! ## 3. Selection of an independent subfamily -/

theorem selection_aux {α : Type} [DecidableEq α] (adj : α → α → Prop) (D : ℕ)
    (hsymm : ∀ x y, adj x y → adj y x) :
    ∀ (n : ℕ) (s : Finset α), s.card ≤ n →
      (∀ x ∈ s, ∃ N : Finset α, N.card ≤ D ∧ ∀ y ∈ s, y ≠ x → adj x y → y ∈ N) →
      ∃ t ⊆ s, s.card ≤ (D + 1) * t.card ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ adj x y := by
  intro n
  induction n with
  | zero =>
    intro s hs _
    refine ⟨∅, Finset.empty_subset _, ?_, by simp⟩
    have : s.card = 0 := by omega
    simp [this]
  | succ n ih =>
    intro s hs hdeg
    rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · exact ⟨∅, Finset.empty_subset _, by simp [h], by simp⟩
    · obtain ⟨N, hN, hNx⟩ := hdeg x hx
      set s' := (s.erase x) \ N with hs'
      have hs's : s' ⊆ s := fun y hy => Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hy).1
      have hc1 : (s.erase x).card ≤ s'.card + N.card := Finset.card_le_card_sdiff_add_card
      have hc2 : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
      have hc3 : s'.card ≤ n := by
        have : s'.card ≤ (s.erase x).card := Finset.card_le_card Finset.sdiff_subset
        omega
      have hdeg' : ∀ y ∈ s', ∃ N' : Finset α, N'.card ≤ D ∧
          ∀ z ∈ s', z ≠ y → adj y z → z ∈ N' := by
        intro y hy
        obtain ⟨N', h1, h2⟩ := hdeg y (hs's hy)
        exact ⟨N', h1, fun z hz hzy hyz => h2 z (hs's hz) hzy hyz⟩
      obtain ⟨t', ht's', hcard, hpair⟩ := ih s' hc3 hdeg'
      have hxt' : x ∉ t' := by
        intro hxt
        have := (Finset.mem_sdiff.mp (ht's' hxt)).1
        simp at this
      have key : ∀ y ∈ t', ¬ adj x y := by
        intro y hy hxy
        have hy' := Finset.mem_sdiff.mp (ht's' hy)
        have hyx : y ≠ x := (Finset.mem_erase.mp hy'.1).1
        exact hy'.2 (hNx y (Finset.mem_erase.mp hy'.1).2 hyx hxy)
      refine ⟨insert x t', ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hs's (ht's' hy)
      · rw [Finset.card_insert_of_notMem hxt']
        nlinarith
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with ha1 | ha2
        · rcases Finset.mem_insert.mp hb with hb1 | hb2
          · exact absurd (ha1.trans hb1.symm) hab
          · rw [ha1]; exact key b hb2
        · rcases Finset.mem_insert.mp hb with hb1 | hb2
          · rw [hb1]; exact fun h => key a ha2 (hsymm _ _ h)
          · exact hpair a ha2 b hb2 hab

theorem independentSelection : IndependentSelection := by
  intro α _ s adj D hsymm hdeg
  exact selection_aux adj D hsymm s.card s le_rfl hdeg

/-! ## 4. Independence on disjoint supports and the tree bound -/

theorem productOnDisjointSupports : ProductOnDisjointSupports := by
  intro Ω X ι mΩ μ _ m hle hind S A hA sel
  classical
  induction sel using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hdisj
    have hdisj' : ∀ ℓ ∈ s, ∀ ℓ' ∈ s, ℓ ≠ ℓ' → Disjoint (S ℓ) (S ℓ') :=
      fun ℓ hℓ ℓ' hℓ' h =>
        hdisj ℓ (Finset.mem_insert_of_mem hℓ) ℓ' (Finset.mem_insert_of_mem hℓ') h
    rw [Finset.set_biInter_insert, Finset.prod_insert ha, ← ih hdisj']
    have hST : Disjoint (S a) (⋃ ℓ ∈ s, S ℓ) := by
      rw [Set.disjoint_iUnion₂_right]
      intro ℓ hℓ
      exact hdisj a (Finset.mem_insert_self a s) ℓ (Finset.mem_insert_of_mem hℓ)
        (fun h => ha (h ▸ hℓ))
    have hInd := indep_iSup_of_disjoint hle hind hST
    rw [Indep_iff] at hInd
    apply hInd
    · exact hA a
    · have hmeas : ∀ ℓ ∈ s, MeasurableSet[⨆ x ∈ ⋃ ℓ ∈ s, S ℓ, m x] (A ℓ) := by
        intro ℓ hℓ
        have hmono : (⨆ x ∈ S ℓ, m x) ≤ ⨆ x ∈ ⋃ ℓ ∈ s, S ℓ, m x :=
          biSup_mono (fun x hx => Set.mem_biUnion hℓ hx)
        exact hmono _ (hA ℓ)
      exact Finset.measurableSet_biInter s hmeas

theorem treeBound : TreeBound := by
  intro Ω X ι mΩ μ _ m hle hind S A hA α C Δ L hα0 hα1 hC hμA trees hcard hL hdeg
  classical
  set β : ℝ := α ^ ((L : ℝ) / ((Δ : ℝ) + 1)) with hβ
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hα0 _
  have htree : ∀ t ∈ trees, μ (⋂ ℓ ∈ t, A ℓ) ≤ ENNReal.ofReal β := by
    intro t ht
    obtain ⟨sel, hsel, hselcard, hselpair⟩ :=
      independentSelection t (fun ℓ ℓ' => ¬ Disjoint (S ℓ) (S ℓ')) Δ
        (fun x y h h' => h h'.symm) (fun ℓ hℓ => hdeg t ht ℓ hℓ)
    have hpairdisj : ∀ ℓ ∈ sel, ∀ ℓ' ∈ sel, ℓ ≠ ℓ' → Disjoint (S ℓ) (S ℓ') := by
      intro ℓ hℓ ℓ' hℓ' hne
      exact not_not.mp (hselpair ℓ hℓ ℓ' hℓ' hne)
    have hsub : (⋂ ℓ ∈ t, A ℓ) ⊆ ⋂ ℓ ∈ sel, A ℓ := by
      intro ω hω
      simp only [Set.mem_iInter] at hω ⊢
      exact fun ℓ hℓ => hω ℓ (hsel hℓ)
    calc μ (⋂ ℓ ∈ t, A ℓ) ≤ μ (⋂ ℓ ∈ sel, A ℓ) := measure_mono hsub
      _ = ∏ ℓ ∈ sel, μ (A ℓ) :=
          productOnDisjointSupports μ m hle hind S A hA sel hpairdisj
      _ ≤ ∏ ℓ ∈ sel, ENNReal.ofReal α := Finset.prod_le_prod (fun ℓ _ => hμA ℓ)
      _ = ENNReal.ofReal (α ^ sel.card) := by
          rw [Finset.prod_const, ENNReal.ofReal_pow hα0]
      _ ≤ ENNReal.ofReal β := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Real.rpow_natCast]
          apply Real.rpow_le_rpow_of_exponent_ge' hα0 hα1 (by positivity)
          rw [div_le_iff₀ (by positivity)]
          have h1 : (t.card : ℝ) ≤ (((Δ + 1) * sel.card : ℕ) : ℝ) := by exact_mod_cast hselcard
          rw [hL t ht] at h1
          push_cast at h1
          linarith
  calc μ (⋃ t ∈ trees, ⋂ ℓ ∈ t, A ℓ) ≤ ∑ t ∈ trees, μ (⋂ ℓ ∈ t, A ℓ) :=
        measure_biUnion_finset_le trees _
    _ ≤ ∑ t ∈ trees, ENNReal.ofReal β := Finset.sum_le_sum htree
    _ = ENNReal.ofReal (trees.card * β) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((C * α ^ (1 / ((Δ : ℝ) + 1))) ^ L) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, ← Real.rpow_natCast (α ^ (1 / ((Δ : ℝ) + 1))) L, ← Real.rpow_mul hα0]
        have e : 1 / ((Δ : ℝ) + 1) * (L : ℝ) = (L : ℝ) / ((Δ : ℝ) + 1) := by ring
        rw [e, ← hβ]
        have hCL : C ^ (L - 1) ≤ C ^ L := pow_le_pow_right₀ hC (Nat.sub_le L 1)
        calc (trees.card : ℝ) * β ≤ C ^ (L - 1) * β := mul_le_mul_of_nonneg_right hcard hβ0
          _ ≤ C ^ L * β := mul_le_mul_of_nonneg_right hCL hβ0

/-! ## 5. The recursion and the pair count of Lemma 4.2 -/

theorem bjRecursion : BjRecursion := by
  intro D u w b hD hu hb hb0 hrec
  have hD' : D ≠ 0 := hD.ne'
  set X := 4 * D * w ^ 2 * u with hX
  have hX0 : 0 ≤ X := by positivity
  have first : ∀ j, b j ≤ D⁻¹ * X ^ (2 ^ j) := by
    intro j
    induction j with
    | zero =>
      have e : D⁻¹ * X = 4 * w ^ 2 * u := by
        rw [hX, show 4 * D * w ^ 2 * u = D * (4 * w ^ 2 * u) by ring, ← mul_assoc,
          inv_mul_cancel₀ hD', one_mul]
      simp only [pow_zero, pow_one]
      rw [e]
      exact hb0
    | succ j ih =>
      have e : X ^ (2 ^ (j + 1)) = (X ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
      calc b (j + 1) ≤ D * b j ^ 2 := hrec j
        _ ≤ D * (D⁻¹ * X ^ (2 ^ j)) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hb j) ih 2) hD.le
        _ = D⁻¹ * X ^ (2 ^ (j + 1)) := by
            rw [e]; field_simp
  intro j
  refine ⟨first j, fun hu' => ?_⟩
  have hX2 : X ^ 2 ≤ u := by
    have h : (4 * D * w ^ 2) ^ 2 * u ≤ 1 := by
      rcases eq_or_lt_of_le (sq_nonneg (4 * D * w ^ 2)) with h0 | h0
      · rw [← h0]; simp
      · calc (4 * D * w ^ 2) ^ 2 * u ≤ (4 * D * w ^ 2) ^ 2 * ((4 * D * w ^ 2) ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hu' h0.le
          _ = 1 := mul_inv_cancel₀ h0.ne'
    calc X ^ 2 = ((4 * D * w ^ 2) ^ 2 * u) * u := by rw [hX]; ring
      _ ≤ 1 * u := mul_le_mul_of_nonneg_right h hu
      _ = u := one_mul u
  have hr : (2 : ℝ) ^ ((j : ℝ) - 1) = (2 : ℝ) ^ j / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  have e : X ^ (2 ^ j) = (X ^ 2) ^ ((2 : ℝ) ^ ((j : ℝ) - 1)) := by
    rw [hr, ← Real.rpow_natCast X 2, ← Real.rpow_mul hX0, ← Real.rpow_natCast X (2 ^ j)]
    congr 1
    push_cast
    ring
  calc b j ≤ D⁻¹ * X ^ (2 ^ j) := first j
    _ = D⁻¹ * (X ^ 2) ^ ((2 : ℝ) ^ ((j : ℝ) - 1)) := by rw [e]
    _ ≤ D⁻¹ * u ^ ((2 : ℝ) ^ ((j : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hX2 (by positivity))
          (inv_nonneg.mpr hD.le)

theorem lemma_4_2_pairCount : Lemma_4_2_PairCount := by
  intro P T n hn
  rw [Nat.choose_two_right]
  have h0 : (2 * P + 3) * (2 * T + 3) ≤ (2 * (P + 2)) * (2 * (T + 2)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h1 : n ≤ 4 * ((P + 2) * (T + 2)) := by
    calc n ≤ (2 * P + 3) * (2 * T + 3) := hn
      _ ≤ (2 * (P + 2)) * (2 * (T + 2)) := h0
      _ = 4 * ((P + 2) * (T + 2)) := by ring
  have h2 : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h3 : n * n ≤ 16 * ((P + 2) * (T + 2)) ^ 2 := by
    calc n * n ≤ (4 * ((P + 2) * (T + 2))) * (4 * ((P + 2) * (T + 2))) := Nat.mul_le_mul h1 h1
      _ = 16 * ((P + 2) * (T + 2)) ^ 2 := by ring
  calc n * (n - 1) / 2 ≤ n * n / 2 := Nat.div_le_div_right h2
    _ ≤ 16 * ((P + 2) * (T + 2)) ^ 2 / 2 := Nat.div_le_div_right h3
    _ = 8 * (P + 2) ^ 2 * (T + 2) ^ 2 := by
        rw [show 16 * ((P + 2) * (T + 2)) ^ 2 = 2 * (8 * (P + 2) ^ 2 * (T + 2) ^ 2) by ring]
        exact Nat.mul_div_cancel_left _ (by norm_num)


/-! ## 6. Numerical choices -/

open Params

theorem pw {w i j : ℕ} (hw : 1 ≤ w) (h : i ≤ j) : w ^ i ≤ w ^ j := Nat.pow_le_pow_right hw h

/-- `c w^k ≤ w^{k+1}` once `c ≤ w`. -/
theorem cpow_le {w c k : ℕ} (hw : c ≤ w) : c * w ^ k ≤ w ^ (k + 1) := by
  rw [pow_succ, mul_comm (w ^ k) w]
  exact Nat.mul_le_mul_right _ hw

theorem num_cavityGain : Num_CavityGain := by
  intro w hw
  have hw1 : (1 : ℤ) ≤ (w : ℤ) := by exact_mod_cast le_trans (by norm_num) hw
  simp only [B, q]
  push_cast
  refine ⟨by ring, by nlinarith⟩

theorem num_flankPass : Num_FlankPass := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  simp only [q, d, B]
  norm_num at h2 ⊢
  nlinarith

theorem num_flankResponseTime : Num_FlankResponseTime := by
  intro w hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have h65 := cpow_le (k := 5) hw
  have a3 := pw (i := 3) (j := 5) hw1 (by norm_num)
  have a2 := pw (i := 2) (j := 5) hw1 (by norm_num)
  have a1 := pw (i := 1) (j := 5) hw1 (by norm_num)
  have a0 := pw (i := 0) (j := 5) hw1 (by norm_num)
  simp only [d, q, d0, A, H0]
  norm_num at h65 a0 a1 ⊢
  nlinarith

theorem num_clearanceTime : Num_ClearanceTime := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  simp only [tc, d, q, H0]
  norm_num at h2 ⊢
  nlinarith

theorem num_responseTime : Num_ResponseTime := by
  intro w hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have h65 := cpow_le (k := 5) hw
  have a3 := pw (i := 3) (j := 5) hw1 (by norm_num)
  have a2 := pw (i := 2) (j := 5) hw1 (by norm_num)
  have a0 := pw (i := 0) (j := 5) hw1 (by norm_num)
  simp only [d0, A, H0, q]
  norm_num at h65 a0 ⊢
  nlinarith

theorem num_cavityLength : Num_CavityLength := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  simp only [q, d]
  norm_num at h2 ⊢
  nlinarith

theorem num_woundBand : Num_WoundBand := by
  intro w hw
  have h3 := cpow_le (k := 2) hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have a0 := pw (i := 0) (j := 2) hw1 (by norm_num)
  have key : 5 * (2 * B w + 40 * q w + 40) < A w := by
    simp only [B, q, A]
    norm_num at h3 a0 ⊢
    nlinarith
  have keyq : ((5 * (2 * B w + 40 * q w + 40) : ℕ) : ℚ) < (A w : ℚ) := by exact_mod_cast key
  push_cast at keyq ⊢
  rw [show (0.2 : ℚ) = 1 / 5 by norm_num]
  linarith

theorem num_seedRatio : Num_SeedRatio := by
  intro w hw
  have hwq : (100000 : ℚ) ≤ (w : ℚ) := by exact_mod_cast hw
  have hw0 : (w : ℚ) ≠ 0 := by intro h; rw [h] at hwq; norm_num at hwq
  constructor
  · simp only [Delta, q, A]
    push_cast
    rw [div_eq_div_iff (pow_ne_zero 3 hw0) hw0]
    ring
  · rw [div_lt_iff₀ (by linarith)]
    norm_num
    linarith

theorem num_seedSpacing : Num_SeedSpacing := by
  intro w hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have e : d1 w = q w * (2 * A w + 4) * (2 * q w + 2) := by simp only [d1, d0, H0]; ring
  have h7 : 4 * w ^ 7 < d1 w := by
    rw [e]
    simp only [q, A]
    have hw0 : 0 < w := by omega
    have p2 : 0 < w ^ 2 := pow_pos hw0 _
    nlinarith [pow_pos hw0 5, pow_pos hw0 4]
  have h6 : w ^ 6 ≤ 4 * w ^ 7 := by
    calc w ^ 6 ≤ w ^ 7 := pw (i := 6) (j := 7) hw1 (by norm_num)
      _ ≤ 4 * w ^ 7 := Nat.le_mul_of_pos_left _ (by norm_num)
  exact ⟨e, h7, lt_of_le_of_lt h6 h7⟩

theorem num_seedCount : Num_SeedCount := by
  intro w hw
  have h3 := cpow_le (k := 2) hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have a0 := pw (i := 0) (j := 2) hw1 (by norm_num)
  simp only [A, Delta, q]
  norm_num at h3 a0 ⊢
  nlinarith

theorem num_epochCost : Num_EpochCost := by
  intro w hw
  have hwq : (10000000000 : ℚ) ≤ (w : ℚ) := by
    have : (10000000000 : ℕ) ≤ w := by norm_num at hw; exact hw
    exact_mod_cast this
  have hden : ((M w : ℕ) : ℚ) - 4 * ((d w : ℕ) : ℚ) - 1 = 496 * (w : ℚ) + 991 := by
    simp only [M, d]; push_cast; ring
  have hnum : ((20 * A w + 2 * M w : ℕ) : ℚ) = 20 * (w : ℚ) ^ 3 + 1024 * w + 2048 := by
    simp only [M, d, A]; push_cast; ring
  have hMq : ((M w : ℕ) : ℚ) = 512 * (w : ℚ) + 1024 := by simp only [M, d]; push_cast; ring
  have hAq : ((A w : ℕ) : ℚ) = (w : ℚ) ^ 3 := by simp only [A]; push_cast; ring
  rw [hden, hnum]
  constructor
  · rw [hMq, div_lt_iff₀ (by positivity)]
    linarith
  · set x : ℚ := (20 * (w : ℚ) ^ 3 + 1024 * w + 2048) / (496 * (w : ℚ) + 991) with hx
    have hx0 : 0 ≤ x := by positivity
    have hceil : (⌈x⌉₊ : ℚ) < x + 1 := Nat.ceil_lt_add_one hx0
    have hxM : x * (512 * (w : ℚ) + 1025) ≤ 2 * (20 * (w : ℚ) ^ 3 + 1024 * w + 2048) := by
      rw [hx, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : (0 : ℚ) ≤ 20 * (w : ℚ) ^ 3 + 1024 * w + 2048 := by positivity
      nlinarith
    have hw0 : (0 : ℚ) ≤ (w : ℚ) := by linarith
    have hw3 : (10000 : ℚ) * (w : ℚ) ≤ (w : ℚ) ^ 3 := by
      have h1 : (10000 : ℚ) ≤ (w : ℚ) ^ 2 := by nlinarith
      calc (10000 : ℚ) * (w : ℚ) ≤ (w : ℚ) ^ 2 * (w : ℚ) := mul_le_mul_of_nonneg_right h1 hw0
        _ = (w : ℚ) ^ 3 := by ring
    have h1 : (((⌈x⌉₊ + 2) * (M w + 1) : ℕ) : ℚ) < ((100 * A w + 4 * (M w + 1) : ℕ) : ℚ) := by
      push_cast
      rw [hMq, hAq]
      have hM0 : (0 : ℚ) < 512 * (w : ℚ) + 1024 + 1 := by positivity
      calc ((⌈x⌉₊ : ℚ) + 2) * (512 * (w : ℚ) + 1024 + 1)
          < (x + 3) * (512 * (w : ℚ) + 1024 + 1) := by
            apply mul_lt_mul_of_pos_right _ hM0; linarith
        _ = x * (512 * (w : ℚ) + 1025) + 3 * (512 * (w : ℚ) + 1025) := by ring
        _ ≤ 2 * (20 * (w : ℚ) ^ 3 + 1024 * w + 2048) + 3 * (512 * (w : ℚ) + 1025) := by
            linarith
        _ ≤ 100 * (w : ℚ) ^ 3 + 4 * (512 * (w : ℚ) + 1024 + 1) := by linarith
    exact_mod_cast h1.le

/-- Exponential beats the degree-15 polynomial at the global choice `w ≥ 10^10`. -/
theorem two_pow_gt (w : ℕ) (hw : 10 ^ 10 ≤ w) : 10 ^ 8 * w ^ 15 < 2 ^ w := by
  have hw' : 10000000000 ≤ w := by norm_num at hw; exact hw
  have hk1 : w < 32 * (w / 32 + 1) := by omega
  have hk2 : 32 * (w / 32) ≤ w := by omega
  have hk3 : 312500000 ≤ w / 32 + 1 := by omega
  have h1 : w / 32 + 1 ≤ 2 ^ (w / 32) := Nat.lt_two_pow_self
  have h2 : (w / 32 + 1) ^ 32 ≤ 2 ^ w := by
    calc (w / 32 + 1) ^ 32 ≤ (2 ^ (w / 32)) ^ 32 := Nat.pow_le_pow_left h1 32
      _ = 2 ^ (32 * (w / 32)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hk2
  have h3 : w ^ 15 < (32 * (w / 32 + 1)) ^ 15 := Nat.pow_lt_pow_left hk1 (by norm_num)
  have h4 : 10 ^ 8 * 32 ^ 15 ≤ (w / 32 + 1) ^ 17 :=
    calc 10 ^ 8 * 32 ^ 15 ≤ 312500000 ^ 17 := by norm_num
      _ ≤ (w / 32 + 1) ^ 17 := Nat.pow_le_pow_left hk3 17
  calc 10 ^ 8 * w ^ 15 < 10 ^ 8 * (32 * (w / 32 + 1)) ^ 15 :=
        (Nat.mul_lt_mul_left (by norm_num)).2 h3
    _ = 10 ^ 8 * 32 ^ 15 * (w / 32 + 1) ^ 15 := by ring
    _ ≤ (w / 32 + 1) ^ 17 * (w / 32 + 1) ^ 15 := Nat.mul_le_mul_right _ h4
    _ = (w / 32 + 1) ^ 32 := by ring
    _ ≤ 2 ^ w := h2

theorem d0_le (w : ℕ) (hw : 1 ≤ w) : d0 w ≤ 24 * w ^ 5 := by
  simp only [d0, A, H0, q]
  have e3 := Nat.one_le_pow 3 w hw
  have e2 := Nat.one_le_pow 2 w hw
  have h1 : 2 * w ^ 3 + 4 ≤ 6 * w ^ 3 := by linarith
  have h2 : 2 * w ^ 2 + 2 ≤ 4 * w ^ 2 := by linarith
  calc (2 * w ^ 3 + 4) * (2 * w ^ 2 + 2) ≤ (6 * w ^ 3) * (4 * w ^ 2) := Nat.mul_le_mul h1 h2
    _ = 24 * w ^ 5 := by ring

theorem d1_le (w : ℕ) (hw : 1 ≤ w) : d1 w ≤ 24 * w ^ 7 := by
  calc d1 w = w ^ 2 * d0 w := rfl
    _ ≤ w ^ 2 * (24 * w ^ 5) := Nat.mul_le_mul_left _ (d0_le w hw)
    _ = 24 * w ^ 7 := by ring

theorem N_le (w : ℕ) (hw : 1 ≤ w) : N w ≤ 4800 * w ^ 10 := by
  calc N w = 200 * w ^ 3 * d1 w := rfl
    _ ≤ 200 * w ^ 3 * (24 * w ^ 7) := Nat.mul_le_mul_left _ (d1_le w hw)
    _ = 4800 * w ^ 10 := by ring

theorem Dtr_le (w : ℕ) (hw : 1 ≤ w) : Dtr w ≤ 4000000 * w ^ 15 := by
  have p : ∀ i, i ≤ 15 → w ^ i ≤ w ^ 15 := fun i hi => pw hw hi
  have e1 : 50 * A w * d1 w ≤ 1200 * w ^ 15 := by
    calc 50 * A w * d1 w = 50 * w ^ 3 * d1 w := rfl
      _ ≤ 50 * w ^ 3 * (24 * w ^ 7) := Nat.mul_le_mul_left _ (d1_le w hw)
      _ = 1200 * w ^ 10 := by ring
      _ ≤ 1200 * w ^ 15 := Nat.mul_le_mul_left _ (p 10 (by norm_num))
  have e2 : 6 * N w + 4 * w ^ 6 + 21 ≤ 28825 * w ^ 10 := by
    have := N_le w hw
    have := p 6 (by norm_num)
    have q6 : w ^ 6 ≤ w ^ 10 := pw hw (by norm_num)
    have q0 : 1 ≤ w ^ 10 := Nat.one_le_pow 10 w hw
    linarith
  have e3 : 5 * d0 w + 1 ≤ 121 * w ^ 5 := by
    have := d0_le w hw
    have q0 : 1 ≤ w ^ 5 := Nat.one_le_pow 5 w hw
    linarith
  have e4 : (6 * N w + 4 * w ^ 6 + 21) * (5 * d0 w + 1) ≤ 3487825 * w ^ 15 := by
    calc (6 * N w + 4 * w ^ 6 + 21) * (5 * d0 w + 1) ≤ (28825 * w ^ 10) * (121 * w ^ 5) :=
          Nat.mul_le_mul e2 e3
      _ = 3487825 * w ^ 15 := by ring
  have e5 : w ^ 6 + 2 * d0 w + 20 ≤ 69 * w ^ 15 := by
    have := d0_le w hw
    have := p 6 (by norm_num)
    have := p 5 (by norm_num)
    have q0 : 1 ≤ w ^ 15 := Nat.one_le_pow 15 w hw
    linarith
  have q1 : 1 ≤ w ^ 15 := Nat.one_le_pow 15 w hw
  simp only [Dtr]
  linarith

theorem num_transportMargin : Num_TransportMargin := by
  intro w hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have hD := Dtr_le w hw1
  have hexp := two_pow_gt w hw
  have hA : A w ≤ w ^ 15 := pw hw1 (by norm_num)
  have hq : q w ≤ w ^ 15 := pw hw1 (by norm_num)
  have hd : d w ≤ 12 * w ^ 15 := by
    have := pw (i := 1) (j := 15) hw1 (by norm_num)
    have q0 : 1 ≤ w ^ 15 := Nat.one_le_pow 15 w hw1
    simp only [d]; rw [pow_one] at this; linarith
  have k1 : (2 * (Dtr w + 10 * A w + 10 * q w) + d w) * 2 < P0 w := by
    simp only [P0]; linarith
  have k2 : (12 * A w + 4 * q w + Dtr w + 10 * A w + 10 * q w) * 2 < P0 w := by
    simp only [P0]; linarith
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; exact_mod_cast k1
  · rw [lt_div_iff₀ (by norm_num)]; exact_mod_cast k2

theorem num_rearWall : Num_RearWall := by
  intro w hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have hexp := two_pow_gt w hw
  have h0 := d0_le w hw1
  have e1 : 3 * v w * d0 w ≤ 72 * w ^ 15 := by
    calc 3 * v w * d0 w = 3 * w ^ 4 * d0 w := rfl
      _ ≤ 3 * w ^ 4 * (24 * w ^ 5) := Nat.mul_le_mul_left _ h0
      _ = 72 * w ^ 9 := by ring
      _ ≤ 72 * w ^ 15 := Nat.mul_le_mul_left _ (pw hw1 (by norm_num))
  have e2 : w ^ 6 ≤ w ^ 15 := pw hw1 (by norm_num)
  have e3 : w ^ 5 ≤ w ^ 15 := pw hw1 (by norm_num)
  have q0 : 1 ≤ w ^ 15 := Nat.one_le_pow 15 w hw1
  have k : (3 * v w * d0 w + 2 * w ^ 6 + 12 * d0 w + 20) * 10 < P w := by
    simp only [P, P0]; linarith
  rw [lt_div_iff₀ (by norm_num)]; exact_mod_cast k

theorem num_ownerCollar : Num_OwnerCollar := by
  refine ⟨by norm_num, by norm_num, fun w hw => ?_⟩
  norm_num at hw
  simp only [m]
  omega

theorem num_commonSpan : Num_CommonSpan := by
  intro w hw
  norm_num at hw
  simp only [m, d]
  omega

theorem num_satelliteWidth : Num_SatelliteWidth := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  simp only [d, q]
  norm_num at h2 ⊢
  nlinarith

theorem num_deficitConstant : Num_DeficitConstant := by
  intro w hw
  norm_num at hw ⊢
  omega

theorem num_recruitment : Num_Recruitment := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  simp only [d, q]
  norm_num at h2 ⊢
  nlinarith

theorem num_advanceDebit : Num_AdvanceDebit := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  have k1 : d w + 4 * (q w + 20) < 5 * q w := by
    simp only [d, q]; norm_num at h2 ⊢; nlinarith
  have k2 : 5 * q w + 10 < B w := by
    simp only [B, q]; norm_num at h2 ⊢; nlinarith
  exact ⟨k1, by omega⟩

theorem num_endpointException : Num_EndpointException := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  simp only [d, q]
  norm_num at h2 ⊢
  nlinarith

theorem num_endGap : Num_EndGap := by
  intro w hw
  have h2 := cpow_le (k := 1) hw
  simp only [Delta, B, d, q]
  norm_num at h2 ⊢
  constructor <;> nlinarith

theorem num_fullBoxHypothesis : Num_FullBoxHypothesis := by
  intro w
  have h1 : w < 2 ^ w := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  simp only [P, P0]
  linarith

end Flagship1D
