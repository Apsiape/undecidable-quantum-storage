import QuantumStorage.Replacement

/-! Theorem 6.7 (`f:forgetting`) and Remark 6.8 (`rem:forgetting-interface`),
conditional abstract form: the extension of Proposition 6.4 and the
full-replacement decomposition on the small systems are explicit hypotheses. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-- Conditional abstract form of Theorem 6.7. Θ indexes the systems of one
window (torus side L and rate eps); `Small` are the finitely many small tori.
Hypotheses: every round channel is CPTP; on the large systems Λ^s has a
two-output equal-marginal extension (Proposition 6.4, one s for all of them);
on the small systems the round channel is a full replacement with weight at
least p > 0 and otherwise a channel. Conclusion: for every η > 0 one time C,
uniform over all systems, after which every encoder and decoder, also after
any further CPTP evolution M (a partial round), has fidelity at most 1/2 + η. C counts rounds; for a period of J elementary layers
the layer cutoff is J * C: write t_layer = J * t + r and take M = the first r layers. -/
theorem uniform_forgetting {Θ : Type} (dim : Θ → ℕ)
    (Λ : (θ : Θ) → QMap (Fin (dim θ)) (Fin (dim θ))) (hΛ : ∀ θ, IsCPTP (Λ θ))
    (Small : Set Θ) (s : ℕ)
    (hExt : ∀ θ, θ ∉ Small → HasEqualMarginalExtension 2 (Λ θ ^ s))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (q : Θ → ℝ) (σ : (θ : Θ) → Mat (Fin (dim θ)))
    (Φ : (θ : Θ) → QMap (Fin (dim θ)) (Fin (dim θ)))
    (hRep : ∀ θ, θ ∈ Small → p ≤ q θ ∧ q θ ≤ 1 ∧ Matrix.trace (σ θ) = 1 ∧
      IsCPTP (Φ θ) ∧
      ∀ ρ, Λ θ ρ = (q θ : ℂ) • (Matrix.trace ρ • σ θ) + (1 - (q θ : ℂ)) • Φ θ ρ)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℕ, ∀ (θ : Θ) (t : ℕ), C ≤ t →
      ∀ M : QMap (Fin (dim θ)) (Fin (dim θ)), IsCPTP M →
      ∀ E : QMap (Fin 2) (Fin (dim θ)), IsCPTP E →
      ∀ D : QMap (Fin (dim θ)) (Fin 2), IsCPTP D →
        entanglementFidelity E (M.comp (Λ θ ^ t)) D ≤ 1 / 2 + η := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hη (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨t0, ht0⟩ := replacement_eventually p hp hp1 η hη
  refine ⟨max (s * j) t0, ?_⟩
  intro θ t ht M hM E hE D hD
  by_cases hθ : θ ∈ Small
  · obtain ⟨hpq, hq1, hσ, hΦ, hdec⟩ := hRep θ hθ
    rw [entanglementFidelity_comp_out]
    have h1 := replacement_ceiling_pow p (q θ) hpq hq1 (Λ θ) (σ θ) hσ (Φ θ) hΦ hdec t
      E hE (D.comp M) (hD.comp hM)
    have h2 := ht0 t (le_of_max_le_right ht)
    linarith
  · have hsj : s * j ≤ t := le_of_max_le_left ht
    have hpow : M.comp (Λ θ ^ t) =
        (M.comp (Λ θ ^ (t - s * j))).comp ((Λ θ ^ s) ^ j) := by
      rw [← pow_mul, LinearMap.comp_assoc]
      congr 1
      rw [← Module.End.mul_eq_comp, ← pow_add, Nat.sub_add_cancel hsj]
    rw [hpow, entanglementFidelity_comp_out]
    have hcl := iterated_cloning_bound_all (dim θ) (Λ θ ^ s) ((hΛ θ).pow s) (hExt θ hθ) j
      E hE (D.comp (M.comp (Λ θ ^ (t - s * j)))) (hD.comp (hM.comp ((hΛ θ).pow _)))
    have hhalf : (1 : ℝ) / 2 ^ (j + 1) ≤ (1 / 2) ^ j := by
      have hpos : (0 : ℝ) < (1 / 2) ^ j := by positivity
      rw [← one_div_pow, pow_succ]
      linarith
    linarith

end QuantumScope
