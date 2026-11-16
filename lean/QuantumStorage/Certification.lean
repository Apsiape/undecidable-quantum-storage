import QuantumStorage.CertificationElementary
import QuantumStorage.CertificationComputability

set_option autoImplicit false
namespace CertificationScope

/-- Exactly the second theorem of the frozen Challenge. The physical inputs
remain explicit hypotheses; the partial-recursive search is proved above. -/
theorem abstract_window_certification
    (u : UniversalInput) (d : Data)
    (hStorage : StorageInput u d) (hForgetting : ForgettingInput u d) :
    (∀ n, RationalCertificate d n ↔ ¬ (u.run n).Dom) ∧
    IsPi01Complete (RationalCertificate d) ∧
    (∀ n, RationalCertificate d n ↔ RealCertificate d n) ∧
    ¬ ComputablePred (RationalCertificate d) := by
  have heq := certificate_iff_nonhalting u d hStorage hForgetting
  refine ⟨heq, ⟨certificate_pi01 d, ?_⟩, rational_iff_real d, ?_⟩
  · intro Q hQ
    obtain ⟨f, hf, hred⟩ := nonhalting_hard u Q hQ
    exact ⟨f, hf, fun n => (hred n).trans (heq (f n)).symm⟩
  · intro h
    exact nonhalting_not_computable u (h.of_eq heq)

#print axioms abstract_window_certification
end CertificationScope
