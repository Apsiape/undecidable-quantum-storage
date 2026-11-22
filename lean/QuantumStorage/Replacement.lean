import QuantumStorage.Iteration
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The full-replacement ceiling 1/4 + (3/4)(1-p)^t (proof of Theorem 6.7,
equation (eq:finite-reset), Section 10 bound (f4:lifetime-upper), Section 18
"Lifetime ceiling"). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-! ### Linearity of the entanglement fidelity in the channel -/

theorem entanglementFidelity_add {α β : Type} [Fintype α] [Fintype β]
    (E : QMap (Fin 2) α) (A B : QMap α β) (D : QMap β (Fin 2)) :
    entanglementFidelity E (A + B) D =
      entanglementFidelity E A D + entanglementFidelity E B D := by
  unfold entanglementFidelity
  have h : amplify 2 (D.comp ((A + B).comp E)) bell =
      amplify 2 (D.comp (A.comp E)) bell + amplify 2 (D.comp (B.comp E)) bell := by
    ext u v
    simp [amplify]
  rw [h, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem entanglementFidelity_smul {α β : Type} [Fintype α] [Fintype β]
    (c : ℝ) (E : QMap (Fin 2) α) (A : QMap α β) (D : QMap β (Fin 2)) :
    entanglementFidelity E ((c : ℂ) • A) D = c * entanglementFidelity E A D := by
  unfold entanglementFidelity
  have h : amplify 2 (D.comp (((c : ℂ) • A).comp E)) bell =
      (c : ℂ) • amplify 2 (D.comp (A.comp E)) bell := by
    ext u v
    simp [amplify]
  rw [h, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- A later channel can be absorbed into the decoder. -/
theorem entanglementFidelity_comp_out {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (E : QMap (Fin 2) α) (T : QMap α β) (M : QMap β γ) (D : QMap γ (Fin 2)) :
    entanglementFidelity E (M.comp T) D = entanglementFidelity E T (D.comp M) := rfl

/-! ### The replacement map and the value 1/4 -/

/-- R_σ(ρ) = tr(ρ) σ. -/
noncomputable def replaceQ {α β : Type} [Fintype α] [Fintype β] (σ : Mat β) : QMap α β where
  toFun ρ := Matrix.trace ρ • σ
  map_add' ρ τ := by rw [Matrix.trace_add, add_smul]
  map_smul' c ρ := by
    rw [Matrix.trace_smul, smul_eq_mul, mul_smul]
    rfl

theorem replaceQ_apply {α β : Type} [Fintype α] [Fintype β] (σ : Mat β) (ρ : Mat α) :
    replaceQ σ ρ = Matrix.trace ρ • σ := rfl

/-- The Bell overlap of a qubit replacement map is tr(τ)/4. -/
theorem bell_overlap_replace (M : QMap (Fin 2) (Fin 2)) (τ : Mat (Fin 2))
    (hM : ∀ ρ, M ρ = Matrix.trace ρ • τ) :
    (Matrix.trace (bell * amplify 2 M bell)).re = (Matrix.trace τ).re / 4 := by
  have h : amplify 2 M bell = fun u v =>
      (if u.1 = v.1 then (1 / 2 : ℂ) else 0) * τ u.2 v.2 := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [amplify, hM, Matrix.smul_apply, smul_eq_mul]
    congr 1
    fin_cases a <;> fin_cases c <;>
      simp [Matrix.trace, bell, Fin.sum_univ_two]
  rw [h]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, bell]
  norm_num
  ring

/-- Trace-preserving form of the value 1/4 (used inside the induction). -/
theorem replacement_fidelity_tp {α β : Type} [Fintype α] [Fintype β]
    (X : QMap α β) (hX : ∀ ρ, Matrix.trace (X ρ) = Matrix.trace ρ)
    (σ : Mat β) (hσ : Matrix.trace σ = 1)
    (R : QMap β β) (hR : ∀ ρ, R ρ = Matrix.trace ρ • σ)
    (E : QMap (Fin 2) α) (hE : ∀ ρ, Matrix.trace (E ρ) = Matrix.trace ρ)
    (D : QMap β (Fin 2)) (hD : ∀ ρ, Matrix.trace (D ρ) = Matrix.trace ρ) :
    entanglementFidelity E (R.comp X) D = 1 / 4 := by
  have hM : ∀ ρ, (D.comp ((R.comp X).comp E)) ρ = Matrix.trace ρ • D σ := by
    intro ρ
    simp only [LinearMap.comp_apply, hR, map_smul, hX, hE]
  unfold entanglementFidelity
  rw [bell_overlap_replace _ (D σ) hM, hD, hσ]
  norm_num

/-- Proof of Theorem 6.7 and Section 18: after a full replacement of the register,
every encoder and decoder has entanglement fidelity exactly 1/4. R is the last map;
evolution after the event is absorbed into the decoder (`entanglementFidelity_comp_out`). -/
theorem replacement_fidelity {α β : Type} [Fintype α] [Fintype β]
    (X : QMap α β) (hX : IsCPTP X) (σ : Mat β) (hσ : Matrix.trace σ = 1)
    (R : QMap β β) (hR : ∀ ρ, R ρ = Matrix.trace ρ • σ)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap β (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (R.comp X) D = 1 / 4 :=
  replacement_fidelity_tp X hX.1 σ hσ R hR E hE.1 D hD.1

/-! ### The ceiling -/

/-- Layer form of the full-replacement ceiling: if layer i replaces the whole
register by σ_i with weight q_i ≥ p and otherwise applies a channel Φ_i, then
after t layers every encoder and decoder has fidelity at most 1/4 + (3/4)(1-p)^t.
Γ t is the composition Λ_{t-1} ∘ ... ∘ Λ_0. Conditional abstract form: hΛ is the operator
form of "the whole register is replaced with probability at least p in each layer,
independently of the other layers"; p > 0 is not needed. -/
theorem replacement_ceiling {α : Type} [Fintype α] (p : ℝ) (t : ℕ)
    (Λ : ℕ → QMap α α) (q : ℕ → ℝ) (σ : ℕ → Mat α) (Φ : ℕ → QMap α α)
    (hq : ∀ i, p ≤ q i ∧ q i ≤ 1) (hσ : ∀ i, Matrix.trace (σ i) = 1)
    (hΦ : ∀ i, IsCPTP (Φ i))
    (hΛ : ∀ i ρ, Λ i ρ = (q i : ℂ) • (Matrix.trace ρ • σ i) + (1 - (q i : ℂ)) • Φ i ρ)
    (Γ : ℕ → QMap α α) (hΓ0 : Γ 0 = LinearMap.id)
    (hΓ : ∀ i, Γ (i + 1) = (Λ i).comp (Γ i))
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap α (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (Γ t) D ≤ 1 / 4 + 3 / 4 * (1 - p) ^ t := by
  have hΛtp : ∀ i ρ, Matrix.trace (Λ i ρ) = Matrix.trace ρ := by
    intro i ρ
    rw [hΛ, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      hσ, (hΦ i).1]
    simp only [smul_eq_mul, mul_one]
    ring
  have hΓtp : ∀ n ρ, Matrix.trace (Γ n ρ) = Matrix.trace ρ := by
    intro n
    induction n with
    | zero => intro ρ; rw [hΓ0]; rfl
    | succ n ih => intro ρ; rw [hΓ, LinearMap.comp_apply, hΛtp, ih]
  induction t generalizing D with
  | zero =>
    have h := (entanglementFidelity_bounds E (Γ 0) D hE
      (by rw [hΓ0]; exact isCPTP_id) hD).2
    norm_num
    linarith
  | succ n ih =>
    obtain ⟨hpq, hq1⟩ := hq n
    have hsplit : Γ (n + 1) = ((q n : ℝ) : ℂ) • ((replaceQ (σ n)).comp (Γ n)) +
        ((1 - q n : ℝ) : ℂ) • ((Φ n).comp (Γ n)) := by
      rw [hΓ]
      apply LinearMap.ext
      intro ρ
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, hΛ,
        replaceQ_apply]
      push_cast
      rfl
    rw [hsplit, entanglementFidelity_add, entanglementFidelity_smul,
      entanglementFidelity_smul,
      replacement_fidelity_tp (Γ n) (hΓtp n) (σ n) (hσ n) (replaceQ (σ n))
        (replaceQ_apply (σ n)) E hE.1 D hD.1,
      entanglementFidelity_comp_out]
    have hih := ih (D.comp (Φ n)) (hD.comp (hΦ n))
    have h1 : 0 ≤ 1 - q n := by linarith
    have h2 : 0 ≤ (1 - p) ^ n := pow_nonneg (by linarith) n
    have h3 : (1 - q n) * entanglementFidelity E (Γ n) (D.comp (Φ n)) ≤
        (1 - q n) * (1 / 4 + 3 / 4 * (1 - p) ^ n) := mul_le_mul_of_nonneg_left hih h1
    have h4 : (1 - q n) * (1 - p) ^ n ≤ (1 - p) * (1 - p) ^ n :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    rw [pow_succ]
    nlinarith

/-- Round form, equation (eq:finite-reset): a channel that is a full replacement
with weight q ≥ p, and otherwise a channel, has
F(E, Λ^t, D) ≤ 1/4 + (3/4)(1-p)^t for every encoder and decoder. -/
theorem replacement_ceiling_pow {α : Type} [Fintype α] (p q : ℝ) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (Λ : QMap α α) (σ : Mat α) (hσ : Matrix.trace σ = 1) (Φ : QMap α α) (hΦ : IsCPTP Φ)
    (hΛ : ∀ ρ, Λ ρ = (q : ℂ) • (Matrix.trace ρ • σ) + (1 - (q : ℂ)) • Φ ρ) (t : ℕ)
    (E : QMap (Fin 2) α) (hE : IsCPTP E) (D : QMap α (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (Λ ^ t) D ≤ 1 / 4 + 3 / 4 * (1 - p) ^ t :=
  replacement_ceiling p t (fun _ => Λ) (fun _ => q) (fun _ => σ) (fun _ => Φ)
    (fun _ => ⟨hpq, hq1⟩) (fun _ => hσ) (fun _ => hΦ) (fun _ => hΛ) (fun n => Λ ^ n)
    (pow_zero Λ) (fun n => pow_succ' Λ n) E hE D hD

/-! ### Lifetime arithmetic -/

/-- Section 10 (f4:lifetime-upper) and Section 18: a time t at which the ceiling
still allows fidelity 7/8 satisfies t ≤ log(6/5)/p < 1/p. -/
theorem replacement_lifetime (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (t : ℕ)
    (h : (7 / 8 : ℝ) ≤ 1 / 4 + 3 / 4 * (1 - p) ^ t) :
    (t : ℝ) ≤ Real.log (6 / 5) / p ∧ Real.log (6 / 5) / p < 1 / p := by
  have h56 : (5 / 6 : ℝ) ≤ (1 - p) ^ t := by linarith
  have hexp : (1 - p) ^ t ≤ Real.exp (-(p * t)) := by
    have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    calc (1 - p) ^ t ≤ Real.exp (-p) ^ t := pow_le_pow_left₀ (by linarith) h1 t
      _ = Real.exp (-(p * t)) := by
        rw [← Real.exp_nat_mul]
        ring_nf
  have hlog : Real.log (5 / 6) ≤ -(p * t) := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith
  have hinv : Real.log (5 / 6) = -Real.log (6 / 5) := by
    rw [← Real.log_inv]
    norm_num
  constructor
  · rw [le_div_iff₀ hp]
    linarith
  · apply div_lt_div_of_pos_right _ hp
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 6 / 5) (by norm_num)
    linarith

/-- The ceiling falls below 1/2 + η after a finite time. -/
theorem replacement_eventually (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t → 1 / 4 + 3 / 4 * (1 - p) ^ t ≤ 1 / 2 + η := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 4 / 3 * (1 / 4 + η) by positivity)
    (show 1 - p < 1 by linarith)
  refine ⟨n, fun t ht => ?_⟩
  have : (1 - p) ^ t ≤ (1 - p) ^ n := pow_le_pow_of_le_one (by linarith) (by linarith) ht
  linarith

/-- Sections 10 and 18, the lifetime bound: under the layer hypotheses of
`replacement_ceiling`, at every time t > log(6/5)/p one constant c < 7/8 bounds the
fidelity of every encoder and decoder, so F*(t) ≤ c < 7/8 and t lies outside the set
whose supremum is tau. Hence tau ≤ log(6/5)/p, and log(6/5)/p < 1/p by
`replacement_lifetime`. -/
theorem replacement_lifetime_layer {α : Type} [Fintype α] (p : ℝ) (hp : 0 < p) (t : ℕ)
    (Λ : ℕ → QMap α α) (q : ℕ → ℝ) (σ : ℕ → Mat α) (Φ : ℕ → QMap α α)
    (hq : ∀ i, p ≤ q i ∧ q i ≤ 1) (hσ : ∀ i, Matrix.trace (σ i) = 1)
    (hΦ : ∀ i, IsCPTP (Φ i))
    (hΛ : ∀ i ρ, Λ i ρ = (q i : ℂ) • (Matrix.trace ρ • σ i) + (1 - (q i : ℂ)) • Φ i ρ)
    (Γ : ℕ → QMap α α) (hΓ0 : Γ 0 = LinearMap.id)
    (hΓ : ∀ i, Γ (i + 1) = (Λ i).comp (Γ i))
    (ht : Real.log (6 / 5) / p < t) :
    ∃ c : ℝ, c < 7 / 8 ∧
      ∀ (E : QMap (Fin 2) α), IsCPTP E → ∀ (D : QMap α (Fin 2)), IsCPTP D →
        entanglementFidelity E (Γ t) D ≤ c := by
  refine ⟨1 / 4 + 3 / 4 * (1 - p) ^ t, ?_, fun E hE D hD =>
    replacement_ceiling p t Λ q σ Φ hq hσ hΦ hΛ Γ hΓ0 hΓ E hE D hD⟩
  by_contra h
  rw [not_lt] at h
  have hp1 : p ≤ 1 := (hq 0).1.trans (hq 0).2
  have hl := (replacement_lifetime p hp hp1 t h).1
  linarith

end QuantumScope
