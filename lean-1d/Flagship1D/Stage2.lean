import Flagship1D.Stage1

/-!
# Proofs: restricted witness trees with dependent stencil flags

Proves `RestrictedWitnessTrees`, `WitnessTreeShape`, `WitnessTreeCount`, `MeshRootCover`,
`ConflictDegreeArea`, `WitnessTreeProbability`, `Q1_L1`, `Q1_L1_Threshold`,
`Lemma_4_2_Probability`, `LeafOverlapDegree`, `ExponentBookkeeping`, `NestedTestSumRaw`.
-/

namespace Flagship1D

open MeasureTheory ProbabilityTheory

/-! ### Separated pairs and the tree family -/

theorem sepPairs_mem {P T : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} :
    pr ∈ sepPairs P T ↔ (pr.1 ∈ childIndex P T ∧ pr.2 ∈ childIndex P T) ∧
      (pr.1.1 < pr.2.1 ∨ (pr.1.1 = pr.2.1 ∧ pr.1.2 < pr.2.2)) ∧
      (pr.1.1 + 2 ≤ pr.2.1 ∨ pr.2.1 + 2 ≤ pr.1.1 ∨ pr.1.2 + 2 ≤ pr.2.2 ∨
        pr.2.2 + 2 ≤ pr.1.2) := by
  simp only [sepPairs, Finset.mem_filter, Finset.mem_product]

theorem sepPairs_ne {P T : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (h : pr ∈ sepPairs P T) :
    pr.1 ≠ pr.2 := by
  rw [sepPairs_mem] at h
  intro he
  have l := h.2.1
  rw [he] at l
  omega

theorem sepPairs_card_le (P T : ℕ) : (sepPairs P T).card ≤ Dpair P T := by
  classical
  have h1 : (sepPairs P T).card ≤ ((childIndex P T).powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn (fun pr => ({pr.1, pr.2} : Finset (ℕ × ℕ)))
    · intro pr hpr
      rw [Finset.mem_coe, sepPairs_mem] at hpr
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpr.1.1
        · exact hpr.1.2
      · apply Finset.card_pair
        intro h
        have l := hpr.2.1
        rw [h] at l
        omega
    · intro pr hpr pr' hpr' heq
      rw [Finset.mem_coe, sepPairs_mem] at hpr hpr'
      simp only at heq
      have ha : pr.1 ∈ ({pr'.1, pr'.2} : Finset (ℕ × ℕ)) := by rw [← heq]; simp
      have hb : pr.2 ∈ ({pr'.1, pr'.2} : Finset (ℕ × ℕ)) := by rw [← heq]; simp
      have ha' : pr'.1 ∈ ({pr.1, pr.2} : Finset (ℕ × ℕ)) := by rw [heq]; simp
      have hb' : pr'.2 ∈ ({pr.1, pr.2} : Finset (ℕ × ℕ)) := by rw [heq]; simp
      have l1 := hpr.2.1
      have l2 := hpr'.2.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ha' hb'
      obtain ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ := pr
      obtain ⟨⟨x1', x2'⟩, ⟨y1', y2'⟩⟩ := pr'
      simp only [Prod.mk.injEq] at ha hb ha' hb' l1 l2 ⊢
      omega
  rw [Finset.card_powersetCard] at h1
  have hn : (childIndex P T).card ≤ (2 * P + 3) * (2 * T + 3) :=
    (lemma_4_2_witness P T 1 0 0 0).1
  exact h1.trans (lemma_4_2_pairCount P T _ hn)

theorem mem_witnessTrees_zero {P T : ℕ} {t : Finset (List (ℕ × ℕ))} :
    t ∈ witnessTrees P T 0 ↔ t = {[]} := by
  simp [witnessTrees]

theorem mem_witnessTrees_succ {P T r : ℕ} {t : Finset (List (ℕ × ℕ))} :
    t ∈ witnessTrees P T (r + 1) ↔ ∃ pr ∈ sepPairs P T, ∃ t1 ∈ witnessTrees P T r,
      ∃ t2 ∈ witnessTrees P T r, t = t1.image (List.cons pr.1) ∪ t2.image (List.cons pr.2) := by
  constructor
  · intro h
    simp only [witnessTrees, Finset.mem_biUnion, Finset.mem_image] at h
    obtain ⟨pr, hpr, tt, htt, rfl⟩ := h
    rw [Finset.mem_product] at htt
    exact ⟨pr, hpr, tt.1, htt.1, tt.2, htt.2, rfl⟩
  · rintro ⟨pr, hpr, t1, h1, t2, h2, rfl⟩
    simp only [witnessTrees, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨pr, hpr, (t1, t2), Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩

theorem witnessTrees_card_leaves (P T : ℕ) :
    ∀ r, ∀ t ∈ witnessTrees P T r, t.card = 2 ^ r
  | 0, t, ht => by rw [mem_witnessTrees_zero] at ht; subst ht; simp
  | r + 1, t, ht => by
    obtain ⟨pr, hpr, t1, h1, t2, h2, rfl⟩ := mem_witnessTrees_succ.mp ht
    have hne := sepPairs_ne hpr
    have hdisj : Disjoint (t1.image (List.cons pr.1)) (t2.image (List.cons pr.2)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_image] at hx1 hx2
      obtain ⟨q, _, rfl⟩ := hx1
      obtain ⟨q', _, hq'⟩ := hx2
      exact hne (List.cons_eq_cons.mp hq').1.symm
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective,
      witnessTrees_card_leaves P T r t1 h1, witnessTrees_card_leaves P T r t2 h2, pow_succ]
    ring

theorem witnessTrees_card (P T : ℕ) :
    ∀ r, (witnessTrees P T r).card ≤ (sepPairs P T).card ^ (2 ^ r - 1)
  | 0 => by simp [witnessTrees]
  | r + 1 => by
    have ih := witnessTrees_card P T r
    have h1 : (witnessTrees P T (r + 1)).card ≤
        ∑ _pr ∈ sepPairs P T, (witnessTrees P T r).card * (witnessTrees P T r).card := by
      simp only [witnessTrees]
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun pr _ => ?_)
      exact Finset.card_image_le.trans (by rw [Finset.card_product])
    rw [Finset.sum_const, smul_eq_mul] at h1
    have h2 : (sepPairs P T).card * ((witnessTrees P T r).card * (witnessTrees P T r).card) ≤
        (sepPairs P T).card * ((sepPairs P T).card ^ (2 ^ r - 1) *
          (sepPairs P T).card ^ (2 ^ r - 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul ih ih)
    have h3 : (sepPairs P T).card * ((sepPairs P T).card ^ (2 ^ r - 1) *
        (sepPairs P T).card ^ (2 ^ r - 1)) = (sepPairs P T).card ^ (2 ^ (r + 1) - 1) := by
      rw [← pow_add, ← pow_succ']
      congr 1
      have := Nat.one_le_two_pow (n := r)
      rw [pow_succ]
      omega
    exact h1.trans (h2.trans h3.le)

theorem witnessTreeCount : WitnessTreeCount := by
  intro P T r
  exact (witnessTrees_card P T r).trans (Nat.pow_le_pow_left (sepPairs_card_le P T) _)

theorem witnessTrees_length (P T : ℕ) :
    ∀ r, ∀ t ∈ witnessTrees P T r, ∀ p ∈ t, p.length = r
  | 0, t, ht, p, hp => by
    rw [mem_witnessTrees_zero] at ht; subst ht
    rw [Finset.mem_singleton] at hp; subst hp; rfl
  | r + 1, t, ht, p, hp => by
    obtain ⟨pr, hpr, t1, h1, t2, h2, rfl⟩ := mem_witnessTrees_succ.mp ht
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      simp [witnessTrees_length P T r t1 h1 q hq]
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      simp [witnessTrees_length P T r t2 h2 q hq]

/-! ### Regions -/

theorem treeRegion_cons (P T w m r : ℕ) (a b : ℤ) (kl : ℕ × ℕ) (p : List (ℕ × ℕ)) :
    treeRegion P T w m (r + 1) a b (kl :: p) =
      box a b (2 * w * P ^ (m + r + 1)) (2 * w * T ^ (m + r + 1)) ∩
        treeRegion P T w m r (a + ((kl.1 * (w * P ^ (m + r)) : ℕ) : ℤ))
          (b + ((kl.2 * (w * T ^ (m + r)) : ℕ) : ℤ)) p := rfl

theorem leafCorner_cons (P T w m r : ℕ) (c : ℤ × ℤ) (kl : ℕ × ℕ) (p : List (ℕ × ℕ)) :
    leafCorner P T w m (r + 1) c (kl :: p) =
      leafCorner P T w m r (c.1 + ((kl.1 * (w * P ^ (m + r)) : ℕ) : ℤ),
        c.2 + ((kl.2 * (w * T ^ (m + r)) : ℕ) : ℤ)) p := rfl

theorem treeRegion_subset_top (P T w m : ℕ) :
    ∀ r a b p, treeRegion P T w m r a b p ⊆ box a b (2 * w * P ^ (m + r)) (2 * w * T ^ (m + r))
  | 0, a, b, p => by intro z hz; exact hz
  | r + 1, a, b, [] => by intro z hz; exact hz
  | r + 1, a, b, kl :: p => by
    rw [treeRegion_cons]
    exact Set.inter_subset_left

theorem mem_cell_max (a : ℤ) (s k k' : ℕ) (hs : 0 < s) (_h1 : k ≤ k' + 1) (h2 : k' ≤ k + 1) :
    a + ((k * s : ℕ) : ℤ) ≤ a + ((max k k' * s : ℕ) : ℤ) ∧
    a + ((max k k' * s : ℕ) : ℤ) < a + ((k * s : ℕ) : ℤ) + ((2 * s : ℕ) : ℤ) := by
  have e1 : k * s ≤ max k k' * s := Nat.mul_le_mul_right _ (le_max_left _ _)
  have e2 : max k k' * s ≤ (k + 1) * s := Nat.mul_le_mul_right _ (max_le (by omega) h2)
  have e1' : ((k * s : ℕ) : ℤ) ≤ ((max k k' * s : ℕ) : ℤ) := by exact_mod_cast e1
  have e2' : ((max k k' * s : ℕ) : ℤ) ≤ (((k + 1) * s : ℕ) : ℤ) := by exact_mod_cast e2
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  push_cast at e1' e2' ⊢
  constructor <;> nlinarith

theorem childBox_disjoint_of_sep {P T w n : ℕ} (a b : ℤ) (kl kl' : ℕ × ℕ)
    (h : kl.1 + 2 ≤ kl'.1 ∨ kl'.1 + 2 ≤ kl.1 ∨ kl.2 + 2 ≤ kl'.2 ∨ kl'.2 + 2 ≤ kl.2) :
    Disjoint (childBox P T w n a b kl) (childBox P T w n a b kl') := by
  rw [Set.disjoint_left]
  intro z h1 h2
  rw [childBox_mem] at h1 h2
  have i1 := idx_close a z.1 _ _ _ h1.1 h2.2.1
  have i2 := idx_close a z.1 _ _ _ h2.1 h1.2.1
  have i3 := idx_close b z.2 _ _ _ h1.2.2.1 h2.2.2.2
  have i4 := idx_close b z.2 _ _ _ h2.2.2.1 h1.2.2.2
  omega

theorem sep_of_childBox_disjoint {P T w n : ℕ} (hP : 1 ≤ P) (hT : 1 ≤ T) (hw : 1 ≤ w)
    (a b : ℤ) (kl kl' : ℕ × ℕ)
    (h : Disjoint (childBox P T w n a b kl) (childBox P T w n a b kl')) :
    kl.1 + 2 ≤ kl'.1 ∨ kl'.1 + 2 ≤ kl.1 ∨ kl.2 + 2 ≤ kl'.2 ∨ kl'.2 + 2 ≤ kl.2 := by
  by_contra hc
  have hs : 0 < w * P ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have ht : 0 < w * T ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  obtain ⟨x1, x2⟩ := mem_cell_max a (w * P ^ n) kl.1 kl'.1 hs (by omega) (by omega)
  obtain ⟨y1, y2⟩ := mem_cell_max b (w * T ^ n) kl.2 kl'.2 ht (by omega) (by omega)
  obtain ⟨x1', x2'⟩ := mem_cell_max a (w * P ^ n) kl'.1 kl.1 hs (by omega) (by omega)
  obtain ⟨y1', y2'⟩ := mem_cell_max b (w * T ^ n) kl'.2 kl.2 ht (by omega) (by omega)
  rw [max_comm kl'.1 kl.1] at x1' x2'
  rw [max_comm kl'.2 kl.2] at y1' y2'
  have hz1 : ((a + ((max kl.1 kl'.1 * (w * P ^ n) : ℕ) : ℤ),
      b + ((max kl.2 kl'.2 * (w * T ^ n) : ℕ) : ℤ)) : ℤ × ℤ) ∈ childBox P T w n a b kl := by
    rw [childBox_mem]; exact ⟨x1, x2, y1, y2⟩
  have hz2 : ((a + ((max kl.1 kl'.1 * (w * P ^ n) : ℕ) : ℤ),
      b + ((max kl.2 kl'.2 * (w * T ^ n) : ℕ) : ℤ)) : ℤ × ℤ) ∈ childBox P T w n a b kl' := by
    rw [childBox_mem]; exact ⟨x1', x2', y1', y2'⟩
  exact Set.disjoint_left.mp h hz1 hz2

theorem witnessTrees_disjoint (P T w m : ℕ) :
    ∀ r, ∀ t ∈ witnessTrees P T r, ∀ (a b : ℤ), ∀ p ∈ t, ∀ p' ∈ t, p ≠ p' →
      Disjoint (treeRegion P T w m r a b p) (treeRegion P T w m r a b p')
  | 0, t, ht, a, b, p, hp, p', hp', hne => by
    rw [mem_witnessTrees_zero] at ht; subst ht
    rw [Finset.mem_singleton] at hp hp'
    exact absurd (hp.trans hp'.symm) hne
  | r + 1, t, ht, a, b, p, hp, p', hp', hne => by
    obtain ⟨pr, hpr, t1, h1, t2, h2, rfl⟩ := mem_witnessTrees_succ.mp ht
    have hsep := (sepPairs_mem.mp hpr).2.2
    have hcd : Disjoint (childBox P T w (m + r) a b pr.1) (childBox P T w (m + r) a b pr.2) :=
      childBox_disjoint_of_sep a b pr.1 pr.2 hsep
    have sub : ∀ (kl : ℕ × ℕ) (q : List (ℕ × ℕ)),
        treeRegion P T w m (r + 1) a b (kl :: q) ⊆ childBox P T w (m + r) a b kl := by
      intro kl q
      rw [treeRegion_cons]
      exact Set.inter_subset_right.trans (treeRegion_subset_top P T w m r _ _ q)
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hp' with hp' | hp'
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
      have hqq : q ≠ q' := fun h => hne (by rw [h])
      rw [treeRegion_cons, treeRegion_cons]
      exact (witnessTrees_disjoint P T w m r t1 h1 _ _ q hq q' hq' hqq).mono
        Set.inter_subset_right Set.inter_subset_right
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
      exact hcd.mono (sub _ _) (sub _ _)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
      exact hcd.symm.mono (sub _ _) (sub _ _)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
      have hqq : q ≠ q' := fun h => hne (by rw [h])
      rw [treeRegion_cons, treeRegion_cons]
      exact (witnessTrees_disjoint P T w m r t2 h2 _ _ q hq q' hq' hqq).mono
        Set.inter_subset_right Set.inter_subset_right

theorem witnessTrees_region_eq (P T w m : ℕ) :
    ∀ r, ∀ t ∈ witnessTrees P T r, ∀ (a b : ℤ), ∀ p ∈ t,
      treeRegion P T w m r a b p =
        box (leafCorner P T w m r (a, b) p).1 (leafCorner P T w m r (a, b) p).2
          (2 * w * P ^ m) (2 * w * T ^ m)
  | 0, t, ht, a, b, p, hp => rfl
  | r + 1, t, ht, a, b, p, hp => by
    obtain ⟨pr, hpr, t1, h1, t2, h2, rfl⟩ := mem_witnessTrees_succ.mp ht
    have hmem := (sepPairs_mem.mp hpr).1
    have hsub := (lemma_4_2_witness P T w (m + r) a b).2.1
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      rw [treeRegion_cons, leafCorner_cons]
      rw [← witnessTrees_region_eq P T w m r t1 h1 _ _ q hq]
      rw [Set.inter_eq_right]
      exact (treeRegion_subset_top P T w m r _ _ q).trans (hsub pr.1 hmem.1)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      rw [treeRegion_cons, leafCorner_cons]
      rw [← witnessTrees_region_eq P T w m r t2 h2 _ _ q hq]
      rw [Set.inter_eq_right]
      exact (treeRegion_subset_top P T w m r _ _ q).trans (hsub pr.2 hmem.2)

theorem witnessTreeShape : WitnessTreeShape := by
  intro P T w _ _ _ m r a b t ht
  exact ⟨witnessTrees_card_leaves P T r t ht,
    fun p hp p' hp' hne => witnessTrees_disjoint P T w m r t ht a b p hp p' hp' hne,
    fun p hp => witnessTrees_region_eq P T w m r t ht a b p hp⟩

/-! ### Restricted witness trees -/

theorem restrictedWitnessTrees : RestrictedWitnessTrees := by
  intro P T w hP hT hw m r
  induction r with
  | zero =>
    intro F a b h
    refine ⟨{[]}, by simp [witnessTrees], ?_⟩
    intro p _
    exact h
  | succ r ih =>
    intro F a b h
    obtain ⟨_, hsub, hwit⟩ := lemma_4_2_witness P T w (m + r) a b
    obtain ⟨kl, hkl, kl', hkl', hdisj, h1, h2⟩ := hwit F h
    have hsep := sep_of_childBox_disjoint hP hT hw a b kl kl' hdisj
    have key : ∀ c ∈ childIndex P T,
        ¬ Sparse P T w (m + r) (F ∩ childBox P T w (m + r) a b c) →
        ∃ t ∈ witnessTrees P T r, ∀ q ∈ t,
          ¬ Sparse P T w m (F ∩ treeRegion P T w m (r + 1) a b (c :: q)) := by
      intro c hc hns
      have e : (F ∩ box a b (2 * w * P ^ (m + r + 1)) (2 * w * T ^ (m + r + 1))) ∩
          childBox P T w (m + r) a b c = F ∩ childBox P T w (m + r) a b c := by
        rw [Set.inter_assoc, Set.inter_eq_right.mpr (hsub c hc)]
      have hns' : ¬ Sparse P T w (m + r)
          ((F ∩ box a b (2 * w * P ^ (m + r + 1)) (2 * w * T ^ (m + r + 1))) ∩
            childBox P T w (m + r) a b c) := by rw [e]; exact hns
      obtain ⟨t, ht, hq⟩ := ih (F ∩ box a b (2 * w * P ^ (m + r + 1)) (2 * w * T ^ (m + r + 1)))
        _ _ hns'
      refine ⟨t, ht, fun q hq' => ?_⟩
      rw [treeRegion_cons, ← Set.inter_assoc]
      exact hq q hq'
    have hne : kl ≠ kl' := by
      intro he; rw [he] at hsep; omega
    by_cases hlex : kl.1 < kl'.1 ∨ (kl.1 = kl'.1 ∧ kl.2 < kl'.2)
    · obtain ⟨t1, ht1, hq1⟩ := key kl hkl h1
      obtain ⟨t2, ht2, hq2⟩ := key kl' hkl' h2
      refine ⟨t1.image (List.cons kl) ∪ t2.image (List.cons kl'), ?_, ?_⟩
      · exact mem_witnessTrees_succ.mpr
          ⟨(kl, kl'), sepPairs_mem.mpr ⟨⟨hkl, hkl'⟩, hlex, hsep⟩, t1, ht1, t2, ht2, rfl⟩
      · intro p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact hq1 q hq
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact hq2 q hq
    · have hcomp : kl.1 ≠ kl'.1 ∨ kl.2 ≠ kl'.2 := by
        by_contra hc
        apply hne
        exact Prod.ext (by omega) (by omega)
      have hlex' : kl'.1 < kl.1 ∨ (kl'.1 = kl.1 ∧ kl'.2 < kl.2) := by omega
      have hsep' : kl'.1 + 2 ≤ kl.1 ∨ kl.1 + 2 ≤ kl'.1 ∨ kl'.2 + 2 ≤ kl.2 ∨
          kl.2 + 2 ≤ kl'.2 := by omega
      obtain ⟨t1, ht1, hq1⟩ := key kl hkl h1
      obtain ⟨t2, ht2, hq2⟩ := key kl' hkl' h2
      refine ⟨t2.image (List.cons kl') ∪ t1.image (List.cons kl), ?_, ?_⟩
      · exact mem_witnessTrees_succ.mpr
          ⟨(kl', kl), sepPairs_mem.mpr ⟨⟨hkl', hkl⟩, hlex', hsep'⟩, t2, ht2, t1, ht1, rfl⟩
      · intro p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact hq2 q hq
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact hq1 q hq

/-! ### Mesh cover -/

theorem cover1Dmesh (a x : ℤ) (s L : ℕ) (hs : 0 < s) :
    ∃ i, i ≤ L / s ∧ ∀ y : ℤ, a ≤ y → y < a + (L : ℤ) → x ≤ y → y < x + (s : ℤ) →
      a + ((i * s : ℕ) : ℤ) ≤ y ∧ y < a + ((i * s : ℕ) : ℤ) + ((2 * s : ℕ) : ℤ) := by
  have hL : L < L / s * s + s := Nat.lt_div_mul_add hs
  obtain ⟨n, hn⟩ : ∃ n, L / s = n := ⟨_, rfl⟩
  rw [hn] at hL ⊢
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have hL' : (L : ℤ) < (n : ℤ) * s + s := by exact_mod_cast hL
  set q := (x - a) / (s : ℤ) with hq
  have h1 : q * s ≤ x - a := Int.ediv_mul_le _ (ne_of_gt hs')
  have h2 : x - a < (q + 1) * s := Int.lt_ediv_add_one_mul_self _ hs'
  rcases lt_or_ge q 0 with hq0 | hq0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    intro y hy1 hy2 hy3 hy4
    have h3 : (q + 1) * (s : ℤ) ≤ 0 := by nlinarith
    push_cast
    constructor <;> nlinarith
  · rcases le_or_gt q (n : ℤ) with hq1 | hq1
    · have hqt : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
      refine ⟨q.toNat, by omega, ?_⟩
      intro y hy1 hy2 hy3 hy4
      push_cast
      rw [hqt]
      constructor <;> nlinarith
    · refine ⟨n, le_rfl, ?_⟩
      intro y hy1 hy2 hy3 hy4
      have h4 : ((n : ℤ) + 1) * s ≤ q * s := by
        apply mul_le_mul_of_nonneg_right _ hs'.le; omega
      push_cast
      constructor <;> nlinarith

theorem meshRootCover : MeshRootCover := by
  intro P T w hP hT hw k E a b L M h
  have hs : 0 < w * P ^ k := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have ht : 0 < w * T ^ k := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have cover : ∀ x y : ℤ, ∃ il ∈ Finset.range (L / (w * P ^ k) + 1) ×ˢ
      Finset.range (M / (w * T ^ k) + 1),
      box a b L M ∩ box x y (w * P ^ k) (w * T ^ k) ⊆ childBox P T w k a b il := by
    intro x y
    obtain ⟨i, hi, hi'⟩ := cover1Dmesh a x (w * P ^ k) L hs
    obtain ⟨l, hl, hl'⟩ := cover1Dmesh b y (w * T ^ k) M ht
    refine ⟨(i, l), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · rintro z ⟨hz1, hz2⟩
      rw [mem_box] at hz1 hz2
      rw [childBox_mem]
      obtain ⟨u1, u2⟩ := hi' z.1 hz1.1 hz1.2.1 hz2.1 hz2.2.1
      obtain ⟨u3, u4⟩ := hl' z.2 hz1.2.2.1 hz1.2.2.2 hz2.2.2.1 hz2.2.2.2
      exact ⟨u1, u2, u3, u4⟩
  cases k with
  | zero =>
    rw [sparse_zero_iff] at h
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr h
    obtain ⟨il, hil, hsub⟩ := cover z.1 z.2
    refine ⟨il, hil, fun h0 => ?_⟩
    rw [sparse_zero_iff] at h0
    have hzQ : z ∈ box z.1 z.2 (w * P ^ 0) (w * T ^ 0) := by
      rw [mem_box]
      have : (1 : ℤ) ≤ w := by exact_mod_cast hw
      simp only [pow_zero, mul_one]
      omega
    have hzz : z ∈ (E ∩ box a b L M) ∩ childBox P T w 0 a b il := ⟨hz, hsub ⟨hz.2, hzQ⟩⟩
    rw [h0] at hzz
    exact hzz
  | succ k =>
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, ∀ c d : ℤ, ¬ Sparse P T w k
        ((E ∩ box a b L M ∩ box x y (w * P ^ (k + 1)) (w * T ^ (k + 1))) \
          box c d (3 * w * P ^ k) (3 * w * T ^ k)) := by
      by_contra hc
      apply h
      rw [sparse_succ_iff]
      intro x y
      by_contra hc2
      exact hc ⟨x, y, fun c d hcd => hc2 ⟨c, d, hcd⟩⟩
    obtain ⟨il, hil, hsub⟩ := cover x y
    refine ⟨il, hil, fun hB => ?_⟩
    rw [sparse_succ_iff] at hB
    obtain ⟨c, d, hcd⟩ := hB x y
    apply hxy c d
    apply sparse_mono P T w k _ hcd
    rintro z ⟨⟨hS, hQ⟩, hJ⟩
    exact ⟨⟨⟨hS, hsub ⟨hS.2, hQ⟩⟩, hQ⟩, hJ⟩

/-! ### The area bound on the conflict degree -/

theorem card_Ico_int (c : ℤ) (n : ℕ) (x : ℕ) :
    (Finset.Ico (c - (x : ℤ)) (c + (n : ℤ) + (x : ℤ))).card = n + 2 * x := by
  rw [Int.card_Ico]; omega

theorem conflictDegreeArea : ConflictDegreeArea := by
  intro κ ι sten pos rx rt w hpos region corner t hreg hdisj ℓ hℓ
  classical
  let E : Finset (ℤ × ℤ) :=
    Finset.Ico ((corner ℓ).1 - ((2 * rx : ℕ) : ℤ)) ((corner ℓ).1 + ((2 * w : ℕ) : ℤ) + ((2 * rx : ℕ) : ℤ)) ×ˢ
      Finset.Ico ((corner ℓ).2 - ((2 * rt : ℕ) : ℤ)) ((corner ℓ).2 + ((2 * w : ℕ) : ℤ) + ((2 * rt : ℕ) : ℤ))
  let conf : Finset ι := t.filter (fun ℓ' => ℓ' ≠ ℓ ∧
    ¬ Disjoint (⋃ q ∈ region ℓ, (sten q : Set κ)) (⋃ q ∈ region ℓ', (sten q : Set κ)))
  refine ⟨conf, ?_, fun ℓ' hℓ' hne hnd => Finset.mem_filter.mpr ⟨hℓ', hne, hnd⟩⟩
  have hpt : ∀ ℓ' ∈ conf, ∃ q', q' ∈ region ℓ' ∧ q' ∈ E := by
    intro ℓ' h
    obtain ⟨_, -, hnd⟩ := Finset.mem_filter.mp h
    obtain ⟨k, hk1, hk2⟩ := Set.not_disjoint_iff.mp hnd
    simp only [Set.mem_iUnion, Finset.mem_coe] at hk1 hk2
    obtain ⟨q, hq, hkq⟩ := hk1
    obtain ⟨q', hq', hkq'⟩ := hk2
    refine ⟨q', hq', ?_⟩
    have hqb := hreg ℓ hℓ hq
    rw [mem_box] at hqb
    obtain ⟨a1, a2⟩ := hpos q k hkq
    obtain ⟨b1, b2⟩ := hpos q' k hkq'
    rw [abs_le] at a1 a2 b1 b2
    simp only [E, Finset.mem_product, Finset.mem_Ico]
    push_cast at hqb ⊢
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  choose! g hg using hpt
  have hinj : Set.InjOn g conf := by
    intro x hx y hy hxy
    by_contra hne
    have hxt := (Finset.mem_filter.mp hx).1
    have hyt := (Finset.mem_filter.mp hy).1
    have hgx := (hg x hx).1
    have hgy := (hg y hy).1
    rw [← hxy] at hgy
    exact Set.disjoint_left.mp (hdisj x hxt y hyt hne) hgx hgy
  have hcard : conf.card ≤ E.card :=
    Finset.card_le_card_of_injOn g (fun x hx => (hg x hx).2) hinj
  have hE : E.card = (2 * w + 4 * rx) * (2 * w + 4 * rt) := by
    simp only [E, Finset.card_product]
    have e1 := card_Ico_int (corner ℓ).1 (2 * w) (2 * rx)
    have e2 := card_Ico_int (corner ℓ).2 (2 * w) (2 * rt)
    rw [e1, e2]
    ring
  rw [hE] at hcard
  have hlt : (2 * w + 4 * rx) * (2 * w + 4 * rt) <
      (2 * w + 4 * rx + 3) * (2 * w + 4 * rt + 3) := by nlinarith
  omega

/-! ### The general probability bound -/

/-- Per-tree product bound (the sharp form behind `treeBound`). -/
theorem perTree_le {Ω X ι : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : X → MeasurableSpace Ω) (hle : ∀ x, m x ≤ mΩ)
    (hind : iIndep m μ) (S : ι → Set X) (A : ι → Set Ω)
    (hA : ∀ ℓ, MeasurableSet[⨆ x ∈ S ℓ, m x] (A ℓ)) (α : ℝ) (Δ : ℕ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hμA : ∀ ℓ, μ (A ℓ) ≤ ENNReal.ofReal α) (t : Finset ι)
    (hdeg : ∀ ℓ ∈ t, ∃ N : Finset ι, N.card ≤ Δ ∧
      ∀ ℓ' ∈ t, ℓ' ≠ ℓ → ¬ Disjoint (S ℓ) (S ℓ') → ℓ' ∈ N) :
    μ (⋂ ℓ ∈ t, A ℓ) ≤ ENNReal.ofReal (α ^ ((t.card : ℝ) / ((Δ : ℝ) + 1))) := by
  classical
  obtain ⟨sel, hsel, hselcard, hselpair⟩ :=
    independentSelection t (fun ℓ ℓ' => ¬ Disjoint (S ℓ) (S ℓ')) Δ
      (fun x y h h' => h h'.symm) hdeg
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
    _ ≤ ∏ _ℓ ∈ sel, ENNReal.ofReal α := Finset.prod_le_prod (fun ℓ _ => hμA ℓ)
    _ = ENNReal.ofReal (α ^ sel.card) := by
        rw [Finset.prod_const, ENNReal.ofReal_pow hα0]
    _ ≤ ENNReal.ofReal (α ^ ((t.card : ℝ) / ((Δ : ℝ) + 1))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_ge' hα0 hα1 (by positivity)
        rw [div_le_iff₀ (by positivity)]
        have h1 : (t.card : ℝ) ≤ (((Δ + 1) * sel.card : ℕ) : ℝ) := by exact_mod_cast hselcard
        push_cast at h1
        linarith

theorem witnessTreeProbability : WitnessTreeProbability := by
  intro Ω κ ι ρ mΩ μ _ X hXm hind e he hrate sten s w hs region corner roots trees NR D N J
    hroots htrees hcard hreg hJ hconf F hF hAe
  classical
  set α : ℝ := (4 * w ^ 2 * s : ℝ) * e with hα
  have hα0 : 0 ≤ α := by positivity
  -- the key set of a leaf, as a finite set
  let pts : ι → Finset (ℤ × ℤ) := fun ℓ =>
    ((Finset.Ico (corner ℓ).1 ((corner ℓ).1 + ((2 * w : ℕ) : ℤ))) ×ˢ
      (Finset.Ico (corner ℓ).2 ((corner ℓ).2 + ((2 * w : ℕ) : ℤ)))).filter (· ∈ region ℓ)
  let K : ι → Finset κ := fun ℓ => (pts ℓ).biUnion sten
  have hKsub : ∀ ℓ, (K ℓ : Set κ) ⊆ ⋃ q ∈ region ℓ, (sten q : Set κ) := by
    intro ℓ k hk
    simp only [K, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hk
    obtain ⟨q, hq, hkq⟩ := hk
    simp only [pts, Finset.mem_filter] at hq
    simp only [Set.mem_iUnion, Finset.mem_coe]
    exact ⟨q, hq.2, hkq⟩
  have hKcard : ∀ ℓ, (K ℓ).card ≤ 4 * w ^ 2 * s := by
    intro ℓ
    have h1 : (K ℓ).card ≤ ∑ q ∈ pts ℓ, (sten q).card := Finset.card_biUnion_le
    have h2 : ∑ q ∈ pts ℓ, (sten q).card ≤ ∑ _q ∈ pts ℓ, s := Finset.sum_le_sum fun q _ => hs q
    have h3 : (pts ℓ).card ≤ (2 * w) * (2 * w) := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Int.card_Ico, Int.card_Ico]
      have e1 : ((corner ℓ).1 + ((2 * w : ℕ) : ℤ) - (corner ℓ).1).toNat = 2 * w := by omega
      have e2 : ((corner ℓ).2 + ((2 * w : ℕ) : ℤ) - (corner ℓ).2).toNat = 2 * w := by omega
      rw [e1, e2]
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h4 : (pts ℓ).card * s ≤ (2 * w) * (2 * w) * s := Nat.mul_le_mul_right _ h3
    calc (K ℓ).card ≤ (pts ℓ).card * s := h1.trans h2
      _ ≤ (2 * w) * (2 * w) * s := h4
      _ = 4 * w ^ 2 * s := by ring
  -- leaf events
  let Aev : ι → Set Ω := fun ℓ => ⋃ k ∈ K ℓ, {ω | X k ω = true}
  have hmeas : ∀ ℓ, MeasurableSet[⨆ k ∈ (K ℓ : Set κ), MeasurableSpace.comap (X k) inferInstance]
      (Aev ℓ) := by
    intro ℓ
    refine Finset.measurableSet_biUnion (K ℓ) (fun k hk => ?_)
    have hle : MeasurableSpace.comap (X k) inferInstance ≤
        ⨆ k ∈ (K ℓ : Set κ), MeasurableSpace.comap (X k) inferInstance :=
      le_iSup₂ (f := fun k (_ : k ∈ (K ℓ : Set κ)) => MeasurableSpace.comap (X k) inferInstance)
        k hk
    exact hle _ ⟨{true}, measurableSet_singleton true, rfl⟩
  have hprob : ∀ ℓ, μ (Aev ℓ) ≤ ENNReal.ofReal α := by
    intro ℓ
    calc μ (Aev ℓ) ≤ ∑ k ∈ K ℓ, μ {ω | X k ω = true} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ K ℓ, ENNReal.ofReal e := Finset.sum_le_sum fun k _ => hrate k
      _ = ENNReal.ofReal ((K ℓ).card * e) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal α := by
          apply ENNReal.ofReal_le_ofReal
          rw [hα]
          have : ((K ℓ).card : ℝ) ≤ ((4 * w ^ 2 * s : ℕ) : ℝ) := by exact_mod_cast hKcard ℓ
          push_cast at this
          exact mul_le_mul_of_nonneg_right this he
  have hindep : iIndep (fun k => MeasurableSpace.comap (X k) inferInstance) μ :=
    (iIndepFun_iff_iIndep _ X μ).mp hind
  have hle : ∀ k, MeasurableSpace.comap (X k) inferInstance ≤ mΩ := fun k => (hXm k).comap_le
  have hJ' : (((J - 1 : ℕ) : ℝ) + 1) = (J : ℝ) := by
    rw [Nat.cast_sub hJ]; push_cast; ring
  -- one tree
  have htree : ∀ x ∈ roots, ∀ t ∈ trees x,
      μ (⋂ ℓ ∈ t, Aev ℓ) ≤ ENNReal.ofReal (α ^ ((N : ℝ) / (J : ℝ))) := by
    intro x hx t ht
    have h := perTree_le μ (fun k => MeasurableSpace.comap (X k) inferInstance) hle hindep
      (fun ℓ => (K ℓ : Set κ)) Aev hmeas α (J - 1) hα0 hAe hprob t (fun ℓ hℓ => by
        obtain ⟨C, hC, hCm⟩ := hconf x hx t ht ℓ hℓ
        exact ⟨C, hC, fun ℓ' hℓ' hne hnd =>
          hCm ℓ' hℓ' hne (fun hd => hnd (hd.mono (hKsub ℓ) (hKsub ℓ')))⟩)
    rw [hJ', hcard x hx t ht] at h
    exact h
  -- the union over roots and trees
  have hcov : F ⊆ ⋃ x ∈ roots, ⋃ t ∈ trees x, ⋂ ℓ ∈ t, Aev ℓ := by
    intro ω hω
    obtain ⟨x, hx, t, ht, hall⟩ := hF ω hω
    simp only [Set.mem_iUnion, Set.mem_iInter]
    refine ⟨x, hx, t, ht, fun ℓ hℓ => ?_⟩
    obtain ⟨q, hq1, hq2⟩ := hall ℓ hℓ
    obtain ⟨k, hk, hXk⟩ := hq1
    have hqb := hreg x hx t ht ℓ hℓ hq2
    rw [mem_box] at hqb
    simp only [Aev, Set.mem_iUnion]
    refine ⟨k, ?_, hXk⟩
    simp only [K, Finset.mem_biUnion]
    refine ⟨q, ?_, hk⟩
    simp only [pts, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
    exact ⟨⟨⟨hqb.1, hqb.2.1⟩, hqb.2.2.1, hqb.2.2.2⟩, hq2⟩
  have hβ0 : 0 ≤ α ^ ((N : ℝ) / (J : ℝ)) := Real.rpow_nonneg hα0 _
  calc μ F ≤ μ (⋃ x ∈ roots, ⋃ t ∈ trees x, ⋂ ℓ ∈ t, Aev ℓ) := measure_mono hcov
    _ ≤ ∑ x ∈ roots, μ (⋃ t ∈ trees x, ⋂ ℓ ∈ t, Aev ℓ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ roots, ∑ t ∈ trees x, μ (⋂ ℓ ∈ t, Aev ℓ) :=
        Finset.sum_le_sum fun x _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ roots, ∑ _t ∈ trees x, ENNReal.ofReal (α ^ ((N : ℝ) / (J : ℝ))) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun t ht => htree x hx t ht
    _ ≤ ∑ _x ∈ roots, ENNReal.ofReal ((D : ℝ) ^ (N - 1) * α ^ ((N : ℝ) / (J : ℝ))) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hβ0
        exact_mod_cast htrees x hx
    _ = ENNReal.ofReal (roots.card * ((D : ℝ) ^ (N - 1) * α ^ ((N : ℝ) / (J : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((NR : ℝ) * (D : ℝ) ^ (N - 1) * α ^ ((N : ℝ) / (J : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hroots

/-! ### The concrete product noise -/

instance keyNoise_isProbabilityMeasure {κ : Type} (p : κ → NNReal) (hp : ∀ k, p k ≤ 1) :
    IsProbabilityMeasure (keyNoise p hp) := by
  unfold keyNoise; infer_instance

theorem keyNoise_iIndepFun {κ : Type} (p : κ → NNReal) (hp : ∀ k, p k ≤ 1) :
    iIndepFun (fun (k : κ) (ω : κ → Bool) => ω k) (keyNoise p hp) := by
  unfold keyNoise
  exact iIndepFun_infinitePi (X := fun _ (b : Bool) => b) (fun _ => measurable_id)

set_option linter.deprecated false in
theorem keyNoise_rate {κ : Type} (p : κ → NNReal) (hp : ∀ k, p k ≤ 1) (k : κ) :
    keyNoise p hp {ω | ω k = true} = (p k : ENNReal) := by
  unfold keyNoise
  have h := (measurePreserving_eval_infinitePi
    (fun k => (PMF.bernoulli (p k) (hp k)).toMeasure) k).measure_preimage
    (measurableSet_singleton true).nullMeasurableSet
  have hset : {ω : κ → Bool | ω k = true} =
      (Function.eval k : (κ → Bool) → Bool) ⁻¹' ({true} : Set Bool) := by
    ext ω; simp
  rw [hset, h, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
  rfl

theorem keyNoise_rate_le {κ : Type} (p : κ → NNReal) (hp : ∀ k, p k ≤ 1) (e : ℝ)
    (hpe : ∀ k, (p k : ℝ) ≤ e) (k : κ) :
    keyNoise p hp {ω | (fun k ω => ω k) k ω = true} ≤ ENNReal.ofReal e := by
  show keyNoise p hp {ω | ω k = true} ≤ ENNReal.ofReal e
  rw [keyNoise_rate, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (hpe k)

/-! ### The tree system of a test rectangle -/

/-- Lower corner of the root mesh box with index `il`. -/
def rootCorner (P T w k : ℕ) (a b : ℤ) (il : ℕ × ℕ) : ℤ × ℤ :=
  (a + ((il.1 * (w * P ^ k) : ℕ) : ℤ), b + ((il.2 * (w * T ^ k) : ℕ) : ℤ))

/-- Leaf region in a test rectangle `W_0 = box a b L M`: `W_0` ∩ leaf box ∩ ancestors. -/
def testRegion (P T w k : ℕ) (a b : ℤ) (L M : ℕ) (x : (ℕ × ℕ) × List (ℕ × ℕ)) :
    Set (ℤ × ℤ) :=
  box a b L M ∩ treeRegion P T w 0 k (rootCorner P T w k a b x.1).1
    (rootCorner P T w k a b x.1).2 x.2

def testCorner (P T w k : ℕ) (a b : ℤ) (x : (ℕ × ℕ) × List (ℕ × ℕ)) : ℤ × ℤ :=
  leafCorner P T w 0 k (rootCorner P T w k a b x.1) x.2

def testTrees (P T k : ℕ) (il : ℕ × ℕ) : Finset (Finset ((ℕ × ℕ) × List (ℕ × ℕ))) :=
  (witnessTrees P T k).image (fun t => t.image (fun q => (il, q)))

theorem mem_testTrees {P T k : ℕ} {il : ℕ × ℕ} {t : Finset ((ℕ × ℕ) × List (ℕ × ℕ))} :
    t ∈ testTrees P T k il ↔ ∃ t0 ∈ witnessTrees P T k, t = t0.image (fun q => (il, q)) := by
  simp only [testTrees, Finset.mem_image]
  constructor
  · rintro ⟨t0, h, rfl⟩; exact ⟨t0, h, rfl⟩
  · rintro ⟨t0, h, rfl⟩; exact ⟨t0, h, rfl⟩

theorem testTrees_card (P T k : ℕ) (il : ℕ × ℕ) :
    (testTrees P T k il).card ≤ Dpair P T ^ (2 ^ k - 1) :=
  Finset.card_image_le.trans (witnessTreeCount P T k)

theorem testTrees_leaves {P T k : ℕ} {il : ℕ × ℕ} {t} (ht : t ∈ testTrees P T k il) :
    t.card = 2 ^ k := by
  obtain ⟨t0, h0, rfl⟩ := mem_testTrees.mp ht
  rw [Finset.card_image_of_injective _ (fun q q' h => (Prod.mk.inj h).2)]
  exact witnessTrees_card_leaves P T k t0 h0

theorem testTrees_region_sub {P T w k : ℕ} {a b : ℤ} {L M : ℕ} {il : ℕ × ℕ} {t}
    (ht : t ∈ testTrees P T k il) :
    ∀ x ∈ t, testRegion P T w k a b L M x ⊆
      box (testCorner P T w k a b x).1 (testCorner P T w k a b x).2 (2 * w) (2 * w) := by
  obtain ⟨t0, h0, rfl⟩ := mem_testTrees.mp ht
  intro x hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  have e := witnessTrees_region_eq P T w 0 k t0 h0 (rootCorner P T w k a b il).1
    (rootCorner P T w k a b il).2 q hq
  intro z hz
  have hz2 := hz.2
  simp only at hz2
  rw [e] at hz2
  simpa [testCorner] using hz2

theorem testTrees_region_disjoint {P T w k : ℕ} {a b : ℤ} {L M : ℕ} {il : ℕ × ℕ} {t}
    (ht : t ∈ testTrees P T k il) :
    ∀ x ∈ t, ∀ y ∈ t, x ≠ y →
      Disjoint (testRegion P T w k a b L M x) (testRegion P T w k a b L M y) := by
  obtain ⟨t0, h0, rfl⟩ := mem_testTrees.mp ht
  intro x hx y hy hne
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hy
  have hqq : q ≠ q' := fun h => hne (by rw [h])
  exact (witnessTrees_disjoint P T w 0 k t0 h0 _ _ q hq q' hq' hqq).mono
    Set.inter_subset_right Set.inter_subset_right

/-- Deterministic part: a failing test rectangle has a root mesh box and a restricted witness
tree whose leaf regions all contain a flag. -/
theorem test_witness {P T w : ℕ} (hP : 1 ≤ P) (hT : 1 ≤ T) (hw : 1 ≤ w) (k : ℕ)
    (S : Set (ℤ × ℤ)) (a b : ℤ) (L M : ℕ) (h : ¬ Sparse P T w k (S ∩ box a b L M)) :
    ∃ il ∈ Finset.range (L / (w * P ^ k) + 1) ×ˢ Finset.range (M / (w * T ^ k) + 1),
      ∃ t ∈ testTrees P T k il, ∀ x ∈ t, (S ∩ testRegion P T w k a b L M x).Nonempty := by
  obtain ⟨il, hil, hroot⟩ := meshRootCover P T w hP hT hw k S a b L M h
  have hroot' : ¬ Sparse P T w (0 + k) ((S ∩ box a b L M) ∩
      box (rootCorner P T w k a b il).1 (rootCorner P T w k a b il).2
        (2 * w * P ^ (0 + k)) (2 * w * T ^ (0 + k))) := by
    rw [Nat.zero_add]; exact hroot
  obtain ⟨t0, ht0, hleaf⟩ := restrictedWitnessTrees P T w hP hT hw 0 k _ _ _ hroot'
  refine ⟨il, hil, t0.image (fun q => (il, q)), mem_testTrees.mpr ⟨t0, ht0, rfl⟩, ?_⟩
  intro x hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  have h0 := hleaf q hq
  rw [sparse_zero_iff] at h0
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr h0
  exact ⟨z, hz.1.1, hz.1.2, hz.2⟩

theorem roots_card_le {P T w k L M : ℕ} (hP : 1 ≤ P) (hT : 1 ≤ T) (hw : 1 ≤ w)
    (hL : L < w * P ^ (k + 1)) (hM : M < w * T ^ (k + 1)) :
    (Finset.range (L / (w * P ^ k) + 1) ×ˢ Finset.range (M / (w * T ^ k) + 1)).card ≤
      4 * (P + 3) * (T + 3) := by
  have hs : 0 < w * P ^ k := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have ht : 0 < w * T ^ k := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have h1 : L / (w * P ^ k) < P := by
    rw [Nat.div_lt_iff_lt_mul hs]
    calc L < w * P ^ (k + 1) := hL
      _ = P * (w * P ^ k) := by ring
  have h2 : M / (w * T ^ k) < T := by
    rw [Nat.div_lt_iff_lt_mul ht]
    calc M < w * T ^ (k + 1) := hM
      _ = T * (w * T ^ k) := by ring
  rw [Finset.card_product, Finset.card_range, Finset.card_range]
  calc (L / (w * P ^ k) + 1) * (M / (w * T ^ k) + 1) ≤ P * T := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ 4 * (P + 3) * (T + 3) := by nlinarith

/-! ### Lemma 12.1 of the quantum storage paper, version 3.0 -/

theorem Dpair_ge_one (P T : ℕ) : 1 ≤ Dpair P T := by
  unfold Dpair
  have h1 := Nat.one_le_pow 2 (P + 2) (by omega)
  have h2 := Nat.one_le_pow 2 (T + 2) (by omega)
  nlinarith

theorem NR_ge_one (P T : ℕ) : 1 ≤ Q1.NR P T := by
  unfold Q1.NR
  nlinarith

theorem pow_two_pow_le (X u : ℝ) (hX0 : 0 ≤ X) (hX2 : X ^ 2 ≤ u) (j : ℕ) :
    X ^ (2 ^ j) ≤ u ^ ((2 : ℝ) ^ ((j : ℝ) - 1)) := by
  have hr : (2 : ℝ) ^ ((j : ℝ) - 1) = (2 : ℝ) ^ j / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  have e : X ^ (2 ^ j) = (X ^ 2) ^ ((2 : ℝ) ^ ((j : ℝ) - 1)) := by
    rw [hr, ← Real.rpow_natCast X 2, ← Real.rpow_mul hX0, ← Real.rpow_natCast X (2 ^ j)]
    congr 1
    push_cast
    ring
  rw [e]
  exact Real.rpow_le_rpow (by positivity) hX2 (by positivity)

theorem q1_arith (NR D A e : ℝ) (J N : ℕ) (hNR : 1 ≤ NR) (hD : 1 ≤ D) (hA : 0 ≤ A)
    (he : 0 ≤ e) (hN : 1 ≤ N) :
    NR * D ^ (N - 1) * (A * e) ^ ((N : ℝ) / (J : ℝ)) ≤
      (NR * D * A ^ (1 / (J : ℝ)) * e ^ (1 / (J : ℝ))) ^ N := by
  have hAe : 0 ≤ A * e := mul_nonneg hA he
  have e1 : NR * D * A ^ (1 / (J : ℝ)) * e ^ (1 / (J : ℝ)) =
      NR * D * (A * e) ^ (1 / (J : ℝ)) := by
    rw [Real.mul_rpow hA he]; ring
  have e2 : ((A * e) ^ (1 / (J : ℝ))) ^ N = (A * e) ^ ((N : ℝ) / (J : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hAe]
    congr 1; ring
  rw [e1, mul_pow, mul_pow, e2]
  have hX : 0 ≤ (A * e) ^ ((N : ℝ) / (J : ℝ)) := Real.rpow_nonneg hAe _
  have h1 : NR ≤ NR ^ N := le_self_pow₀ hNR (by omega)
  have h2 : D ^ (N - 1) ≤ D ^ N := pow_le_pow_right₀ hD (Nat.sub_le N 1)
  have h3 : 0 ≤ D ^ (N - 1) := by positivity
  calc NR * D ^ (N - 1) * (A * e) ^ ((N : ℝ) / (J : ℝ))
      ≤ NR ^ N * D ^ N * (A * e) ^ ((N : ℝ) / (J : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hX
        exact mul_le_mul h1 h2 h3 (by positivity)

theorem q1_l1 : Q1_L1 := by
  intro P T w s rx rt hP hT hw hs κ sten pos hcard hpos p hp e he hpe j hj a b L M hL hM
  classical
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hNR : (1 : ℝ) ≤ (Q1.NR P T : ℝ) := by exact_mod_cast NR_ge_one P T
  have hD : (1 : ℝ) ≤ (Q1.DR P T : ℝ) := by exact_mod_cast Dpair_ge_one P T
  have hJpos : 0 < Q1.JR w rx rt := by simp only [Q1.JR]; positivity
  have hA0 : (0 : ℝ) ≤ (Q1.AR w s : ℝ) := by positivity
  have hzR : Q1.zR P T w s rx rt (k + 1) e =
      ((Q1.NR P T : ℝ) * (Q1.DR P T : ℝ) * (Q1.AR w s : ℝ) ^ (1 / (Q1.JR w rx rt : ℝ)) *
        e ^ (1 / (Q1.JR w rx rt : ℝ))) ^ (2 ^ k) := by
    simp only [Q1.zR, Q1.CR, Q1.cR, Nat.add_sub_cancel]
  rw [hzR]
  by_cases hAe : (4 * w ^ 2 * s : ℝ) * e ≤ 1
  · have main := witnessTreeProbability (keyNoise p hp) (fun k ω => ω k)
      (fun k => measurable_pi_apply k) (keyNoise_iIndepFun p hp) e he
      (keyNoise_rate_le p hp e hpe) sten s w hcard (testRegion P T w k a b L M)
      (testCorner P T w k a b)
      (Finset.range (L / (w * P ^ k) + 1) ×ˢ Finset.range (M / (w * T ^ k) + 1))
      (testTrees P T k) (Q1.NR P T) (Q1.DR P T) (2 ^ k) (Q1.JR w rx rt)
      (roots_card_le hP hT hw hL hM) (fun x _ => testTrees_card P T k x)
      (fun x _ t ht => testTrees_leaves ht) (fun x _ t ht => testTrees_region_sub ht)
      hJpos
      (fun x _ t ht ℓ hℓ => conflictDegreeArea sten pos rx rt w hpos _ _ t
        (testTrees_region_sub ht) (testTrees_region_disjoint ht) ℓ hℓ)
      {ω | ¬ Sparse P T w k (stencilFlags sten ω ∩ box a b L M)}
      (fun ω hω => test_witness hP hT hw k _ a b L M hω) hAe
    refine main.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA : (4 * w ^ 2 * s : ℝ) = (Q1.AR w s : ℝ) := by simp [Q1.AR]
    rw [hA]
    exact q1_arith _ _ _ e _ _ hNR hD hA0 he Nat.one_le_two_pow
  · replace hAe := not_le.mp hAe
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hA : (4 * w ^ 2 * s : ℝ) = (Q1.AR w s : ℝ) := by simp [Q1.AR]
    rw [hA] at hAe
    have hb : 1 ≤ (Q1.NR P T : ℝ) * (Q1.DR P T : ℝ) *
        (Q1.AR w s : ℝ) ^ (1 / (Q1.JR w rx rt : ℝ)) * e ^ (1 / (Q1.JR w rx rt : ℝ)) := by
      rw [mul_assoc _ ((Q1.AR w s : ℝ) ^ _), ← Real.mul_rpow hA0 he]
      have h1 : 1 ≤ ((Q1.AR w s : ℝ) * e) ^ (1 / (Q1.JR w rx rt : ℝ)) :=
        Real.one_le_rpow hAe.le (by positivity)
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by
          apply mul_le_mul (mul_le_mul hNR hD zero_le_one (by positivity)) h1 zero_le_one
          positivity
    exact one_le_pow₀ hb

theorem q1_l1_threshold : Q1_L1_Threshold := by
  intro P T w s rx rt hw hs e he hle
  have hA : (0 : ℝ) < (Q1.AR w s : ℝ) := by
    simp only [Q1.AR]; push_cast; positivity
  have hND : (1 : ℝ) ≤ ((2 * Q1.NR P T * Q1.DR P T : ℕ) : ℝ) := by
    have h1 := NR_ge_one P T
    have h2 := Dpair_ge_one P T
    have : 1 ≤ 2 * Q1.NR P T * Q1.DR P T := by unfold Q1.DR; nlinarith
    exact_mod_cast this
  have hJpos : 0 < Q1.JR w rx rt := by simp only [Q1.JR]; positivity
  set X : ℝ := ((2 * Q1.NR P T * Q1.DR P T : ℕ) : ℝ) with hX
  have hX0 : 0 < X := by linarith
  have hzp : X ^ (-(Q1.JR w rx rt : ℤ)) = (X ^ Q1.JR w rx rt)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hAe : (Q1.AR w s : ℝ) * e ≤ (X ^ Q1.JR w rx rt)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hle hA.le
    rw [Q1.eR0, ← hX, hzp, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
    exact this
  have hXJ : 1 ≤ X ^ Q1.JR w rx rt := one_le_pow₀ hND
  refine ⟨?_, hAe.trans (inv_le_one_of_one_le₀ hXJ)⟩
  have hAe0 : 0 ≤ (Q1.AR w s : ℝ) * e := mul_nonneg hA.le he
  have h1 : ((Q1.AR w s : ℝ) * e) ^ (1 / (Q1.JR w rx rt : ℝ)) ≤ X⁻¹ := by
    calc ((Q1.AR w s : ℝ) * e) ^ (1 / (Q1.JR w rx rt : ℝ))
        ≤ ((X ^ Q1.JR w rx rt)⁻¹) ^ (1 / (Q1.JR w rx rt : ℝ)) :=
          Real.rpow_le_rpow hAe0 hAe (by positivity)
      _ = X⁻¹ := by
          rw [Real.inv_rpow (by positivity), one_div,
            Real.pow_rpow_inv_natCast hX0.le (by omega)]
  have hCR : Q1.CR P T w s rx rt * e ^ Q1.cR w rx rt =
      (Q1.NR P T : ℝ) * (Q1.DR P T : ℝ) * ((Q1.AR w s : ℝ) * e) ^ (1 / (Q1.JR w rx rt : ℝ)) := by
    simp only [Q1.CR, Q1.cR]
    rw [Real.mul_rpow hA.le he]; ring
  rw [hCR]
  have hND0 : (0 : ℝ) ≤ (Q1.NR P T : ℝ) * (Q1.DR P T : ℝ) := by positivity
  calc (Q1.NR P T : ℝ) * (Q1.DR P T : ℝ) * ((Q1.AR w s : ℝ) * e) ^ (1 / (Q1.JR w rx rt : ℝ))
      ≤ (Q1.NR P T : ℝ) * (Q1.DR P T : ℝ) * X⁻¹ := mul_le_mul_of_nonneg_left h1 hND0
    _ = 1 / 2 := by
      rw [hX]; push_cast
      have hN0 : (0 : ℝ) < (Q1.NR P T : ℝ) := by simp only [Q1.NR]; positivity
      have hD0 : (0 : ℝ) < (Q1.DR P T : ℝ) := by simp only [Q1.DR, Dpair]; positivity
      field_simp

/-! ### Lemma 4.2 of the classical construction (Douglas and Mghirbi, version 2.0.0), probabilistic part (independent replacement flags) -/

theorem bj_algebra (D Y : ℝ) (hD : 0 < D) (N : ℕ) (hN : 1 ≤ N) :
    D ^ (N - 1) * Y ^ N = D⁻¹ * (D * Y) ^ N := by
  rw [mul_pow]
  have h : D ^ N = D ^ (N - 1) * D := by rw [← pow_succ]; congr 1; omega
  rw [h]
  field_simp

theorem stencilFlags_self (ω : ℤ × ℤ → Bool) :
    stencilFlags (fun q => ({q} : Finset (ℤ × ℤ))) ω = {z | ω z = true} := by
  ext z; simp [stencilFlags]

/-- The doubled-box bound `b_j ≤ D^{-1}(4Dw²u)^{2^j}` from the general theorem with `J = 1`. -/
theorem doubledBox_bound {P T w : ℕ} (hP : 1 ≤ P) (hT : 1 ≤ T) (hw : 1 ≤ w)
    (p : ℤ × ℤ → NNReal) (hp : ∀ z, p z ≤ 1) (u : ℝ) (hu : 0 ≤ u) (hpu : ∀ z, (p z : ℝ) ≤ u)
    (j : ℕ) (a b : ℤ) :
    keyNoise p hp
        {ω | ¬ Sparse P T w j ({z | ω z = true} ∩ box a b (2 * w * P ^ j) (2 * w * T ^ j))} ≤
      ENNReal.ofReal ((Dpair P T : ℝ)⁻¹ * (4 * (Dpair P T : ℝ) * w ^ 2 * u) ^ (2 ^ j)) := by
  classical
  have hD : (1 : ℝ) ≤ (Dpair P T : ℝ) := by exact_mod_cast Dpair_ge_one P T
  have hD0 : (0 : ℝ) < (Dpair P T : ℝ) := by linarith
  by_cases hAe : (4 * w ^ 2 * (1 : ℕ) : ℝ) * u ≤ 1
  · -- the tree system with the single root (0,0) and W_0 = the doubled box itself
    have main := witnessTreeProbability (keyNoise p hp) (fun k ω => ω k)
      (fun k => measurable_pi_apply k) (keyNoise_iIndepFun p hp) u hu
      (keyNoise_rate_le p hp u hpu) (fun q => ({q} : Finset (ℤ × ℤ))) 1 w (fun q => by simp)
      (testRegion P T w j a b (2 * w * P ^ j) (2 * w * T ^ j)) (testCorner P T w j a b)
      ({(0, 0)} : Finset (ℕ × ℕ)) (testTrees P T j) 1 (Dpair P T) (2 ^ j) 1
      (by simp) (fun x _ => testTrees_card P T j x)
      (fun x _ t ht => testTrees_leaves ht) (fun x _ t ht => testTrees_region_sub ht) le_rfl
      (fun x _ t ht ℓ hℓ => ⟨∅, by simp, fun ℓ' hℓ' hne hnd => by
        exfalso; apply hnd
        have hd := testTrees_region_disjoint (w := w) (a := a) (b := b)
          (L := 2 * w * P ^ j) (M := 2 * w * T ^ j) ht ℓ hℓ ℓ' hℓ' (Ne.symm hne)
        simp only [Finset.coe_singleton]
        rw [Set.disjoint_left] at hd ⊢
        intro k hk hk'
        simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hk hk'
        obtain ⟨q, hq, rfl⟩ := hk
        obtain ⟨q', hq', hqq⟩ := hk'
        rw [← hqq] at hq'
        exact hd hq hq'⟩)
      {ω | ¬ Sparse P T w j (stencilFlags (fun q => ({q} : Finset (ℤ × ℤ))) ω ∩
        box a b (2 * w * P ^ j) (2 * w * T ^ j))}
      (fun ω hω => by
        refine ⟨(0, 0), Finset.mem_singleton_self _, ?_⟩
        have hroot : ¬ Sparse P T w (0 + j)
            ((stencilFlags (fun q => ({q} : Finset (ℤ × ℤ))) ω ∩
              box a b (2 * w * P ^ j) (2 * w * T ^ j)) ∩
            box (rootCorner P T w j a b (0, 0)).1 (rootCorner P T w j a b (0, 0)).2
              (2 * w * P ^ (0 + j)) (2 * w * T ^ (0 + j))) := by
          simp only [rootCorner, zero_mul, Nat.cast_zero, add_zero, Nat.zero_add,
            Set.inter_assoc, Set.inter_self]
          exact hω
        obtain ⟨t0, ht0, hleaf⟩ := restrictedWitnessTrees P T w hP hT hw 0 j _ _ _ hroot
        refine ⟨t0.image (fun q => ((0, 0), q)), mem_testTrees.mpr ⟨t0, ht0, rfl⟩, ?_⟩
        intro x hx
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
        have h0 := hleaf q hq
        rw [sparse_zero_iff] at h0
        obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr h0
        exact ⟨z, hz.1.1, hz.1.2, hz.2⟩) hAe
    simp only [stencilFlags_self] at main
    refine main.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have hN : (((2 ^ j : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = ((2 ^ j : ℕ) : ℝ) := by simp
    rw [hN, Real.rpow_natCast]
    calc _ = (Dpair P T : ℝ) ^ (2 ^ j - 1) * (4 * (w : ℝ) ^ 2 * u) ^ (2 ^ j) := by
          push_cast; ring
      _ = (Dpair P T : ℝ)⁻¹ * ((Dpair P T : ℝ) * (4 * (w : ℝ) ^ 2 * u)) ^ (2 ^ j) :=
          bj_algebra _ _ hD0 _ Nat.one_le_two_pow
      _ = _ := by ring
  · replace hAe := not_le.mp hAe
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    push_cast at hAe
    have h1 : (Dpair P T : ℝ) ≤ 4 * (Dpair P T : ℝ) * w ^ 2 * u := by nlinarith
    have h2 : (Dpair P T : ℝ) ^ (2 ^ j) ≤ (4 * (Dpair P T : ℝ) * w ^ 2 * u) ^ (2 ^ j) :=
      pow_le_pow_left₀ hD0.le h1 _
    have h3 : (Dpair P T : ℝ) ≤ (Dpair P T : ℝ) ^ (2 ^ j) :=
      le_self_pow₀ hD (by positivity)
    rw [le_inv_mul_iff₀ hD0, mul_one]
    linarith

theorem lemma_4_2_probability : Lemma_4_2_Probability := by
  intro P T w hP hT hw p hp u hu hpu
  have hD : (1 : ℝ) ≤ (Dpair P T : ℝ) := by exact_mod_cast Dpair_ge_one P T
  have hD0 : (0 : ℝ) < (Dpair P T : ℝ) := by linarith
  refine ⟨fun j a b => doubledBox_bound hP hT hw p hp u hu hpu j a b, fun hsmall => ?_⟩
  -- (ii) the threshold form
  have hX2 : (4 * (Dpair P T : ℝ) * w ^ 2 * u) ^ 2 ≤ u := by
    have h : (4 * (Dpair P T : ℝ) * w ^ 2) ^ 2 * u ≤ 1 := by
      have hpos : 0 < (4 * (Dpair P T : ℝ) * w ^ 2) ^ 2 := by
        have : (1 : ℝ) ≤ w := by exact_mod_cast hw
        positivity
      calc (4 * (Dpair P T : ℝ) * w ^ 2) ^ 2 * u
          ≤ (4 * (Dpair P T : ℝ) * w ^ 2) ^ 2 * ((4 * (Dpair P T : ℝ) * w ^ 2) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hsmall hpos.le
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    calc (4 * (Dpair P T : ℝ) * w ^ 2 * u) ^ 2 = ((4 * (Dpair P T : ℝ) * w ^ 2) ^ 2 * u) * u := by
          ring
      _ ≤ 1 * u := mul_le_mul_of_nonneg_right h hu
      _ = u := one_mul u
  have hX0 : 0 ≤ 4 * (Dpair P T : ℝ) * w ^ 2 * u := by positivity
  have hpow : ∀ j : ℕ, (4 * (Dpair P T : ℝ) * w ^ 2 * u) ^ (2 ^ j) ≤
      u ^ ((2 : ℝ) ^ ((j : ℝ) - 1)) := fun j => pow_two_pow_le _ u hX0 hX2 j
  have part2 : ∀ (j : ℕ) (a b : ℤ),
      keyNoise p hp
          {ω | ¬ Sparse P T w j ({z | ω z = true} ∩ box a b (2 * w * P ^ j) (2 * w * T ^ j))} ≤
        ENNReal.ofReal ((Dpair P T : ℝ)⁻¹ * u ^ ((2 : ℝ) ^ ((j : ℝ) - 1))) := by
    intro j a b
    refine (doubledBox_bound hP hT hw p hp u hu hpu j a b).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (hpow j) (inv_nonneg.mpr hD0.le)
  refine ⟨part2, fun mx my j a b => ?_⟩
  -- (iii) the fixed-multiple cover
  classical
  set R := Finset.range (mx * P ^ (j + 1) / (w * P ^ j) + 1) ×ˢ
    Finset.range (my * T ^ (j + 1) / (w * T ^ j) + 1) with hR
  have hsub : {ω : ℤ × ℤ → Bool | ¬ Sparse P T w j
      ({z | ω z = true} ∩ box a b (mx * P ^ (j + 1)) (my * T ^ (j + 1)))} ⊆
      ⋃ il ∈ R, {ω | ¬ Sparse P T w j ({z | ω z = true} ∩
        box (rootCorner P T w j a b il).1 (rootCorner P T w j a b il).2
          (2 * w * P ^ j) (2 * w * T ^ j))} := by
    intro ω hω
    obtain ⟨il, hil, hroot⟩ := meshRootCover P T w hP hT hw j _ a b _ _ hω
    refine Set.mem_iUnion₂.mpr ⟨il, hil, fun hs => hroot ?_⟩
    apply sparse_mono P T w j _ hs
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have hRcard : R.card ≤ (mx * P + 1) * (my * T + 1) := by
    rw [hR, Finset.card_product, Finset.card_range, Finset.card_range]
    have hs : 0 < w * P ^ j := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have ht : 0 < w * T ^ j := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have h1 : mx * P ^ (j + 1) / (w * P ^ j) ≤ mx * P := by
      apply Nat.div_le_of_le_mul
      calc mx * P ^ (j + 1) = (mx * P) * P ^ j := by ring
        _ = 1 * (P ^ j * (mx * P)) := by ring
        _ ≤ w * (P ^ j * (mx * P)) := Nat.mul_le_mul_right _ hw
        _ = (w * P ^ j) * (mx * P) := by ring
    have h2 : my * T ^ (j + 1) / (w * T ^ j) ≤ my * T := by
      apply Nat.div_le_of_le_mul
      calc my * T ^ (j + 1) = (my * T) * T ^ j := by ring
        _ = 1 * (T ^ j * (my * T)) := by ring
        _ ≤ w * (T ^ j * (my * T)) := Nat.mul_le_mul_right _ hw
        _ = (w * T ^ j) * (my * T) := by ring
    exact Nat.mul_le_mul (by omega) (by omega)
  have hβ : 0 ≤ (Dpair P T : ℝ)⁻¹ * u ^ ((2 : ℝ) ^ ((j : ℝ) - 1)) := by positivity
  have hexp : (2 : ℝ) ^ ((j : ℝ) - 1) = (1 / 2 : ℝ) * 2 ^ j := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]; ring
  calc keyNoise p hp {ω | ¬ Sparse P T w j
        ({z | ω z = true} ∩ box a b (mx * P ^ (j + 1)) (my * T ^ (j + 1)))}
      ≤ keyNoise p hp (⋃ il ∈ R, {ω | ¬ Sparse P T w j ({z | ω z = true} ∩
          box (rootCorner P T w j a b il).1 (rootCorner P T w j a b il).2
            (2 * w * P ^ j) (2 * w * T ^ j))}) := measure_mono hsub
    _ ≤ ∑ il ∈ R, keyNoise p hp {ω | ¬ Sparse P T w j ({z | ω z = true} ∩
          box (rootCorner P T w j a b il).1 (rootCorner P T w j a b il).2
            (2 * w * P ^ j) (2 * w * T ^ j))} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _il ∈ R, ENNReal.ofReal ((Dpair P T : ℝ)⁻¹ * u ^ ((2 : ℝ) ^ ((j : ℝ) - 1))) :=
        Finset.sum_le_sum fun il _ => part2 j _ _
    _ = ENNReal.ofReal (R.card * ((Dpair P T : ℝ)⁻¹ * u ^ ((2 : ℝ) ^ ((j : ℝ) - 1)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((((mx * P + 1) * (my * T + 1) : ℕ) : ℝ) / (Dpair P T : ℝ) *
          u ^ ((1 / 2 : ℝ) * 2 ^ j)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← hexp, div_eq_mul_inv, mul_assoc]
        apply mul_le_mul_of_nonneg_right _ hβ
        exact_mod_cast hRcard

end Flagship1D
