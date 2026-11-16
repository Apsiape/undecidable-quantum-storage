import QuantumStorage.BellExpectation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-- Paper v2, Lemma 6.6, with the exact frozen statement and channel definitions. -/
theorem bell_sharing_bound
    (a b k : ℕ) (hk : 0 < k)
    (T : QMap (Fin a) (Fin b)) (hT : IsCPTP T)
    (hExt : HasEqualMarginalExtension k T)
    (E : QMap (Fin 2) (Fin a)) (hE : IsCPTP E)
    (D : QMap (Fin b) (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E T D ≤ (1 / 2 : ℝ) + 1 / (2 * (k : ℝ)) := by
  obtain ⟨ρ, hρ, hTrace, hMarg⟩ := decoded_reference_state k T hExt E hE D hD
  have hb := bellProjector_state_bound k ρ hρ hTrace
  have hf : ∀ j : Fin k,
      (Matrix.trace (bellProjector k j * ρ)).re = entanglementFidelity E T D := by
    intro j
    rw [trace_bellProjector, hMarg]
    rfl
  simp_rw [hf] at hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have heq : (k : ℝ) * ((1 / 2 : ℝ) + 1 / (2 * (k : ℝ))) = ((k : ℝ) + 1) / 2 := by
    field_simp
  nlinarith

end QuantumScope
