import QuantumStorage.Definitions
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false
namespace CertificationScope

/-- The paper's nonhalting storage premise implies every rational test. -/
theorem certificate_of_nonhalting (u : UniversalInput) (d : Data)
    (hs : StorageInput u d) (n : ℕ) (hn : ¬ (u.run n).Dom) :
    RationalCertificate d n := by
  intro L t q hL ht hlo hhi
  have h := hs n hn L t q hL ht hlo hhi
  linarith

/-- A halting input has a failed finite test at the midpoint of its window. -/
theorem nonhalting_of_certificate (u : UniversalInput) (d : Data)
    (hf : ForgettingInput u d) (n : ℕ) (h : RationalCertificate d n) :
    ¬ (u.run n).Dom := by
  intro hn
  obtain ⟨T, hT⟩ := hf n hn
  obtain ⟨N, hN⟩ := exists_nat_ge ((T : ℚ) / d.c)
  let L := max (d.L0 n) N
  have hL : d.L0 n ≤ L := Nat.le_max_left _ _
  have hNL : (N : ℚ) ≤ (L : ℚ) := by exact_mod_cast Nat.le_max_right (d.L0 n) N
  have ht : (T : ℚ) ≤ d.c * (L : ℚ) := by
    have hh := (div_le_iff₀ d.c_pos).mp (hN.trans hNL)
    simpa [mul_comm] using hh
  let q := (d.lo n + d.hi n) / 2
  have hlo : d.lo n < q := by dsimp [q]; linarith [(d.window n).2.1]
  have hhi : q < d.hi n := by dsimp [q]; linarith [(d.window n).2.1]
  have hlow := h L T q hL ht hlo hhi
  have hupp := hT L T q (le_refl T) hlo hhi
  linarith

theorem certificate_iff_nonhalting (u : UniversalInput) (d : Data)
    (hs : StorageInput u d) (hf : ForgettingInput u d) (n : ℕ) :
    RationalCertificate d n ↔ ¬ (u.run n).Dom :=
  ⟨nonhalting_of_certificate u d hf n, certificate_of_nonhalting u d hs n⟩

/-- Coercing coefficients and the rational argument commutes with evaluation. -/
theorem eval_rat_cast (p : Polynomial ℚ) (q : ℚ) :
    (p.map (algebraMap ℚ ℝ)).eval (q : ℝ) = ((p.eval q : ℚ) : ℝ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (algebraMap ℚ ℝ) q

/-- Polynomial continuity and rational density remove the rate restriction. -/
theorem rational_iff_real (d : Data) (n : ℕ) :
    RationalCertificate d n ↔ RealCertificate d n := by
  constructor
  · intro h L t x hL ht hlo hhi
    by_contra hx
    have hx' : ((d.polynomial n L t).map (algebraMap ℚ ℝ)).eval x < (7 / 8 : ℝ) :=
      lt_of_not_ge hx
    let p := (d.polynomial n L t).map (algebraMap ℚ ℝ)
    let U : Set ℝ := {y | (d.lo n : ℝ) < y ∧ y < (d.hi n : ℝ) ∧ p.eval y < 7 / 8}
    have ho : IsOpen U :=
      (isOpen_lt continuous_const continuous_id).inter
        ((isOpen_lt continuous_id continuous_const).inter
          (isOpen_lt p.continuous continuous_const))
    have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    obtain ⟨y, hy, q, hq⟩ := hd.inter_open_nonempty U ho ⟨x, hlo, hhi, hx'⟩
    subst y
    have hqlo : d.lo n < q := by exact_mod_cast hy.1
    have hqhi : q < d.hi n := by exact_mod_cast hy.2.1
    have hbound := h L t q hL ht hqlo hqhi
    have hbound' : (7 / 8 : ℝ) ≤ p.eval (q : ℝ) := by
      dsimp [p]
      rw [eval_rat_cast]
      convert (Rat.cast_le (K := ℝ)).2 hbound using 1; norm_num
    exact (not_lt_of_ge hbound') hy.2.2
  · intro h L t q hL ht hlo hhi
    have hlo' : (d.lo n : ℝ) < (q : ℝ) := by exact_mod_cast hlo
    have hhi' : (q : ℝ) < (d.hi n : ℝ) := by exact_mod_cast hhi
    have hb := h L t (q : ℝ) hL ht hlo' hhi'
    rw [eval_rat_cast] at hb
    apply (Rat.cast_le (K := ℝ)).1
    convert hb using 1; norm_num

/-- The exact test accepts precisely the certificate's guarded inequalities. -/
theorem certificate_iff_tests (d : Data) (n : ℕ) :
    RationalCertificate d n ↔ ∀ L t k, d.test (n, L, t, k) = true := by
  constructor
  · intro h L t k
    apply (d.test_spec n L t k).2
    rintro ⟨hL, ht, hlo, hhi⟩
    exact h L t (d.rate k) hL ht hlo hhi
  · intro h L t q hL ht hlo hhi
    obtain ⟨k, rfl⟩ := d.rate_surjective q
    exact (d.test_spec n L t k).1 (h L t k) ⟨hL, ht, hlo, hhi⟩

end CertificationScope
