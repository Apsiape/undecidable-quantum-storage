import QuantumStorage.BellSharing
import Mathlib.Logic.Equiv.Fin.Basic

/-! Lemma 6.5 (`f:iteration`): iteration of equal-marginal extensions, and its
composition with Lemma 6.6. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-! ### Channel facts used below -/

theorem isCPTP_id {α : Type} [Fintype α] : IsCPTP (LinearMap.id : QMap α α) := by
  refine ⟨fun _ => rfl, fun r ρ hρ => ?_⟩
  have h : amplify r (LinearMap.id : QMap α α) ρ = ρ := rfl
  rw [h]
  exact hρ

theorem IsCPTP.pow {α : Type} [Fintype α] {T : QMap α α} (hT : IsCPTP T) :
    ∀ n : ℕ, IsCPTP (T ^ n)
  | 0 => by
    rw [pow_zero]
    exact isCPTP_id
  | n + 1 => by
    rw [show T ^ (n + 1) = (T ^ n).comp T from pow_succ T n]
    exact (hT.pow n).comp hT

/-- A channel with at least one equal marginal is itself CPTP. -/
theorem HasEqualMarginalExtension.isCPTP {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] {k : ℕ} {T : QMap α β} (hk : 0 < k)
    (h : HasEqualMarginalExtension k T) : IsCPTP T := by
  obtain ⟨S, hS, hSm⟩ := h
  have hT : T = (marginalQ k ⟨0, hk⟩).comp S := by
    apply LinearMap.ext
    intro ρ
    rw [LinearMap.comp_apply, marginalQ_apply, hSm]
  rw [hT]
  exact (marginalQ_cptp k ⟨0, hk⟩).comp hS

theorem HasEqualMarginalExtension.of_eq {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] {k k' : ℕ} (hkk : k = k') {T : QMap α β}
    (h : HasEqualMarginalExtension k T) : HasEqualMarginalExtension k' T := hkk ▸ h

/-! ### Flattening k blocks of m outputs into k*m outputs -/

/-- `w ↦ (n ↦ w i l)` where `n = finProdFinEquiv (i, l)`. -/
def flattenOutputs (k m : ℕ) (γ : Type) : (Fin k → Fin m → γ) ≃ (Fin (k * m) → γ) :=
  (Equiv.curry (Fin k) (Fin m) γ).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl γ))

theorem flattenOutputs_apply (k m : ℕ) {γ : Type} (w : Fin k → Fin m → γ)
    (i : Fin k) (l : Fin m) :
    flattenOutputs k m γ w (finProdFinEquiv (i, l)) = w i l := by
  simp [flattenOutputs, Equiv.arrowCongr_apply]

theorem flattenOutputs_update (k m : ℕ) {γ : Type} (w : Fin k → Fin m → γ)
    (i : Fin k) (l : Fin m) (y : γ) :
    Function.update (flattenOutputs k m γ w) (finProdFinEquiv (i, l)) y =
      flattenOutputs k m γ (Function.update w i (Function.update (w i) l y)) := by
  funext n
  obtain ⟨⟨i', l'⟩, rfl⟩ := finProdFinEquiv.surjective n
  rw [flattenOutputs_apply]
  by_cases h : (i', l') = (i, l)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp
  · rw [Function.update_of_ne (finProdFinEquiv.injective.ne h), flattenOutputs_apply]
    by_cases hi : i' = i
    · subst hi
      have hl : l' ≠ l := fun hl => h (by rw [hl])
      simp [Function.update_of_ne hl]
    · simp [Function.update_of_ne hi]

/-- The marginal of a flattened output pair is the nested marginal. -/
theorem marginal_flatten {γ : Type} [Fintype γ] [DecidableEq γ]
    (k m : ℕ) (i : Fin k) (l : Fin m) (ρ : Mat (Fin k → Fin m → γ)) :
    marginal (k * m) (finProdFinEquiv (i, l)) (reindexQ (flattenOutputs k m γ) ρ) =
      marginal m l (marginal k i ρ) := by
  classical
  ext x y
  have hL : marginal (k * m) (finProdFinEquiv (i, l))
      (reindexQ (flattenOutputs k m γ) ρ) x y =
      ∑ w : Fin k → Fin m → γ, if w i l = x then
        ρ w (Function.update w i (Function.update (w i) l y)) else 0 := by
    unfold marginal
    rw [← (flattenOutputs k m γ).sum_comp]
    apply Finset.sum_congr rfl
    intro w _
    rw [flattenOutputs_apply, flattenOutputs_update]
    simp [reindexQ, Matrix.submatrix_apply]
  have hR : marginal m l (marginal k i ρ) x y =
      ∑ w : Fin k → Fin m → γ, if w i l = x then
        ρ w (Function.update w i (Function.update (w i) l y)) else 0 := by
    show (∑ u : Fin m → γ, if u l = x then (∑ w : Fin k → Fin m → γ,
      if w i = u then ρ w (Function.update w i (Function.update u l y)) else 0) else 0) = _
    calc (∑ u : Fin m → γ, if u l = x then (∑ w : Fin k → Fin m → γ,
          if w i = u then ρ w (Function.update w i (Function.update u l y)) else 0) else 0)
        = ∑ u : Fin m → γ, ∑ w : Fin k → Fin m → γ, (if w i = u then
            (if u l = x then ρ w (Function.update w i (Function.update u l y)) else 0)
            else 0) := by
          apply Finset.sum_congr rfl
          intro u _
          by_cases h1 : u l = x
          · simp only [h1, ite_true]
          · simp only [h1, ite_false, ite_self, Finset.sum_const_zero]
      _ = ∑ w : Fin k → Fin m → γ, ∑ u : Fin m → γ, (if w i = u then
            (if u l = x then ρ w (Function.update w i (Function.update u l y)) else 0)
            else 0) := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.sum_ite_eq]
          simp
  rw [hL, hR]

/-! ### Lemma 6.5 -/

/-- Composition form: a k-output extension of T and an m-output extension of U
give a (k*m)-output extension of U ∘ T. -/
theorem equalMarginalExtension_comp {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (k m : ℕ) (T : QMap α β) (U : QMap β γ)
    (hT : HasEqualMarginalExtension k T) (hU : HasEqualMarginalExtension m U) :
    HasEqualMarginalExtension (k * m) (U.comp T) := by
  obtain ⟨S, hS, hSm⟩ := hT
  obtain ⟨V, hV, hVm⟩ := hU
  refine ⟨(reindexQ (flattenOutputs k m γ)).comp ((tensorPowerQ V k).comp S),
    (reindexQ_cptp _).comp ((tensorPowerQ_cptp V hV k).comp hS), ?_⟩
  intro n ρ
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective n
  change marginal (k * m) (finProdFinEquiv (i, l))
    (reindexQ (flattenOutputs k m γ) (tensorPowerQ V k (S ρ))) = U (T ρ)
  rw [marginal_flatten, marginal_tensorPowerQ V hV, hSm, hVm]

/-- The identity has a one-output extension. -/
theorem extension_one_id {α : Type} [Fintype α] [DecidableEq α] :
    HasEqualMarginalExtension 1 (LinearMap.id : QMap α α) := by
  refine ⟨reindexQ (Equiv.funUnique (Fin 1) α).symm, reindexQ_cptp _, ?_⟩
  intro j ρ
  ext x y
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  unfold marginal
  rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
  simp [reindexQ, Matrix.submatrix_apply]

/-- Lemma 6.5 for every natural j (j = 0 is the one-output identity). -/
theorem iteration_extension_all {α : Type} [Fintype α] [DecidableEq α]
    (T : QMap α α) (hExt : HasEqualMarginalExtension 2 T) :
    ∀ j : ℕ, HasEqualMarginalExtension (2 ^ j) (T ^ j)
  | 0 => by
    rw [pow_zero, pow_zero]
    exact extension_one_id
  | j + 1 => by
    rw [show T ^ (j + 1) = (T ^ j).comp T from pow_succ T j]
    exact (equalMarginalExtension_comp 2 (2 ^ j) T (T ^ j) hExt
      (iteration_extension_all T hExt j)).of_eq (by ring)

/-- Paper Lemma 6.5 (`f:iteration`), as printed: a two-output equal-marginal
extension of T gives a 2^j-output equal-marginal extension of T^j for every
positive integer j. -/
theorem iteration_extension {α : Type} [Fintype α] [DecidableEq α]
    (T : QMap α α) (hExt : HasEqualMarginalExtension 2 T) (j : ℕ) (hj : 1 ≤ j) :
    HasEqualMarginalExtension (2 ^ j) (T ^ j) := by
  cases j with
  | zero => omega
  | succ j => exact iteration_extension_all T hExt (j + 1)

/-! ### Lemma 6.5 composed with Lemma 6.6 -/

theorem iterated_cloning_bound_all (a : ℕ) (T : QMap (Fin a) (Fin a)) (hT : IsCPTP T)
    (hExt : HasEqualMarginalExtension 2 T) (j : ℕ)
    (E : QMap (Fin 2) (Fin a)) (hE : IsCPTP E)
    (D : QMap (Fin a) (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (T ^ j) D ≤ (1 / 2 : ℝ) + 1 / 2 ^ (j + 1) := by
  have h := bell_sharing_bound a a (2 ^ j) (by positivity) (T ^ j) (hT.pow j)
    (iteration_extension_all T hExt j) E hE D hD
  have heq : (1 : ℝ) / (2 * ((2 ^ j : ℕ) : ℝ)) = 1 / 2 ^ (j + 1) := by
    push_cast
    ring
  rw [heq] at h
  exact h

/-- Lemmas 6.5 and 6.6 together, the step "Proposition 6.4 and Lemmas 6.5-6.6
give the bound at time j s_n" of Theorem 6.7: if T has a two-output
equal-marginal extension, every encoder and decoder through T^j has
entanglement fidelity at most 1/2 + 2^{-j-1}. The hypothesis hT is implied by hExt
(`HasEqualMarginalExtension.isCPTP`); it is kept to mirror the word "channel". -/
theorem iterated_cloning_bound (a : ℕ) (T : QMap (Fin a) (Fin a)) (hT : IsCPTP T)
    (hExt : HasEqualMarginalExtension 2 T) (j : ℕ) (hj : 1 ≤ j)
    (E : QMap (Fin 2) (Fin a)) (hE : IsCPTP E)
    (D : QMap (Fin a) (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (T ^ j) D ≤ (1 / 2 : ℝ) + 1 / 2 ^ (j + 1) := by
  cases j with
  | zero => omega
  | succ j => exact iterated_cloning_bound_all a T hT hExt (j + 1) E hE D hD

end QuantumScope
