import QuantumStorage.Replacement

/-! The good-event fidelity bound (proof of Lemma 16.1, `q1:l18`): if the
channel is a mixture of CPTP branches with input-independent weights and on a
set G of branches the encoded, transmitted and decoded map is the identity,
the entanglement fidelity is at least the weight of G. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

theorem entanglementFidelity_zero {α β : Type} [Fintype α] [Fintype β]
    (E : QMap (Fin 2) α) (D : QMap β (Fin 2)) :
    entanglementFidelity E (0 : QMap α β) D = 0 := by
  have h := entanglementFidelity_smul 0 E (0 : QMap α β) D
  simpa using h

theorem entanglementFidelity_sum {α β ι : Type} [Fintype α] [Fintype β]
    (E : QMap (Fin 2) α) (D : QMap β (Fin 2)) (w : ι → ℝ) (B : ι → QMap α β)
    (s : Finset ι) :
    entanglementFidelity E (∑ i ∈ s, (w i : ℂ) • B i) D =
      ∑ i ∈ s, w i * entanglementFidelity E (B i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using entanglementFidelity_zero E D
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, entanglementFidelity_add,
      entanglementFidelity_smul, ih]

/-- The identity logical channel has entanglement fidelity one. -/
theorem entanglementFidelity_of_identity {α β : Type} [Fintype α] [Fintype β]
    (E : QMap (Fin 2) α) (T : QMap α β) (D : QMap β (Fin 2))
    (h : D.comp (T.comp E) = LinearMap.id) :
    entanglementFidelity E T D = 1 := by
  unfold entanglementFidelity
  rw [h]
  have ha : amplify 2 (LinearMap.id : QMap (Fin 2) (Fin 2)) bell = bell := rfl
  rw [ha, bell_mul_self, bell_trace]
  simp

/-- Proof of Lemma 16.1 ("the unconditional overlap is at least one minus these
two probabilities"), abstract channel form: a channel that is a mixture of CPTP
branches with nonnegative input-independent weights, such that on the branches
in G the recovery returns the encoded state exactly, has entanglement fidelity
at least the total weight of G. Encoder-side failure (Lemma 17.3(b)) is covered by
taking α = Fin 2, E = id and T = Λ ∘ E_phys over the joint coupling outcomes. -/
theorem good_event_fidelity {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ι → QMap α β) (hB : ∀ i, IsCPTP (B i))
    (T : QMap α β) (hT : T = ∑ i, (w i : ℂ) • B i) (G : Finset ι)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap β (Fin 2)) (hD : IsCPTP D)
    (hG : ∀ i ∈ G, D.comp ((B i).comp E) = LinearMap.id) :
    ∑ i ∈ G, w i ≤ entanglementFidelity E T D := by
  classical
  rw [hT, entanglementFidelity_sum]
  calc ∑ i ∈ G, w i = ∑ i ∈ G, w i * entanglementFidelity E (B i) D := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [entanglementFidelity_of_identity E (B i) D (hG i hi), mul_one]
    _ ≤ ∑ i, w i * entanglementFidelity E (B i) D := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
        intro i _ _
        exact mul_nonneg (hw i) (entanglementFidelity_bounds E (B i) D hE (hB i) hD).1

/-- Proof of Lemma 16.1 (`q1:l18`), as printed: "its unconditional overlap is at
least one minus these two probabilities". The weights are a probability vector;
every branch outside the good set G lies in one of two failure events F₁, F₂
(initialization failure and the top bad tests). -/
theorem good_event_fidelity_union {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (B : ι → QMap α β) (hB : ∀ i, IsCPTP (B i))
    (T : QMap α β) (hT : T = ∑ i, (w i : ℂ) • B i) (G F₁ F₂ : Finset ι)
    (hcover : ∀ i, i ∉ G → i ∈ F₁ ∨ i ∈ F₂)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap β (Fin 2)) (hD : IsCPTP D)
    (hG : ∀ i ∈ G, D.comp ((B i).comp E) = LinearMap.id) :
    1 - ∑ i ∈ F₁, w i - ∑ i ∈ F₂, w i ≤ entanglementFidelity E T D := by
  classical
  have hgood := good_event_fidelity w hw B hB T hT G E hE D hD hG
  have hsplit := Finset.sum_add_sum_compl G w
  have hsub : Gᶜ ⊆ F₁ ∪ F₂ := by
    intro i hi
    rcases hcover i (Finset.mem_compl.mp hi) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  have h1 : ∑ i ∈ Gᶜ, w i ≤ ∑ i ∈ F₁ ∪ F₂, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hw i)
  have h2 := Finset.sum_union_inter (s₁ := F₁) (s₂ := F₂) (f := w)
  have h3 : 0 ≤ ∑ i ∈ F₁ ∩ F₂, w i := Finset.sum_nonneg (fun i _ => hw i)
  linarith

end QuantumScope
