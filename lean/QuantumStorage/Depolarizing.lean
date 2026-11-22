import QuantumStorage.Witnesses

/-! T11: the tensor power of a depolarizing-type channel eps R_sigma + (1-eps) id
over N factors is eps^N times a full replacement plus (1-eps^N) times a channel
(Definitions 2.2-2.3; "simultaneous replacement of every factor has probability
at least (inf I_n)^{R_n}", proof of Theorem 6.7). A replacement absorbs any
preceding trace-preserving layer, so every noisy layer meets the hypotheses of
`replacement_ceiling`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
namespace QuantumScope

/-! ### Linearity of `tensorQ` -/

theorem tensorQ_apply {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (T : QMap α β) (U : QMap γ δ) (ρ : Mat (α × γ)) (x y : β × δ) :
    tensorQ T U ρ x y =
      T (fun a b => U (fun c d => ρ (a, c) (b, d)) x.2 y.2) x.1 y.1 := rfl

theorem tensorQ_add_left {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A B : QMap α β) (U : QMap γ δ) :
    tensorQ (A + B) U = tensorQ A U + tensorQ B U := by
  apply LinearMap.ext
  intro ρ
  ext x y
  rw [LinearMap.add_apply, Matrix.add_apply, tensorQ_apply, tensorQ_apply, tensorQ_apply]
  rfl

theorem tensorQ_smul_left {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (c : ℂ) (A : QMap α β) (U : QMap γ δ) :
    tensorQ (c • A) U = c • tensorQ A U := by
  apply LinearMap.ext
  intro ρ
  ext x y
  rw [LinearMap.smul_apply, Matrix.smul_apply, tensorQ_apply, tensorQ_apply]
  rfl

theorem tensorQ_add_right {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (T : QMap α β) (A B : QMap γ δ) :
    tensorQ T (A + B) = tensorQ T A + tensorQ T B := by
  apply LinearMap.ext
  intro ρ
  ext x y
  rw [LinearMap.add_apply, Matrix.add_apply, tensorQ_apply, tensorQ_apply, tensorQ_apply,
    ← Matrix.add_apply, ← map_add]
  rfl

theorem tensorQ_smul_right {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (c : ℂ) (T : QMap α β) (A : QMap γ δ) :
    tensorQ T (c • A) = c • tensorQ T A := by
  apply LinearMap.ext
  intro ρ
  ext x y
  rw [LinearMap.smul_apply, Matrix.smul_apply, tensorQ_apply, tensorQ_apply,
    ← Matrix.smul_apply, ← map_smul]
  rfl

/-- The tensor product of two replacement maps is the replacement by the product state. -/
theorem tensorQ_replaceQ {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (σ : Mat β) (τ : Mat δ) :
    tensorQ (replaceQ σ : QMap α β) (replaceQ τ : QMap γ δ) = replaceQ (σ ⊗ₖ τ) := by
  apply LinearMap.ext
  intro ρ
  ext x y
  rw [tensorQ_apply, replaceQ_apply, replaceQ_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, replaceQ_apply, Matrix.kroneckerMap_apply,
    Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-! ### Convex combinations of channels -/

theorem isCPTP_combo {α β : Type} [Fintype α] [Fintype β] (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) (A B : QMap α β) (hA : IsCPTP A) (hB : IsCPTP B) :
    IsCPTP ((a : ℂ) • A + (b : ℂ) • B) := by
  constructor
  · intro ρ
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, hA.1, hB.1, smul_eq_mul, smul_eq_mul, ← add_mul,
      ← Complex.ofReal_add, hab, Complex.ofReal_one, one_mul]
  · intro r ρ hρ
    have h : amplify r ((a : ℂ) • A + (b : ℂ) • B) ρ =
        (a : ℂ) • amplify r A ρ + (b : ℂ) • amplify r B ρ := by
      ext u v
      simp [amplify]
    rw [h]
    exact ((hA.2 r ρ hρ).smul (Complex.zero_le_real.mpr ha)).add
      ((hB.2 r ρ hρ).smul (Complex.zero_le_real.mpr hb))

/-- A nonnegative combination of two channels is its total weight times a channel. -/
theorem exists_cptp_combo {α β : Type} [Fintype α] [Fintype β] (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (A B : QMap α β) (hA : IsCPTP A) (hB : IsCPTP B) :
    ∃ Ψ : QMap α β, IsCPTP Ψ ∧ (a : ℂ) • A + (b : ℂ) • B = ((a + b : ℝ) : ℂ) • Ψ := by
  by_cases h : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    refine ⟨A, hA, ?_⟩
    rw [h, ha0, hb0]
    simp
  · have hpos : 0 < a + b := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨((a / (a + b) : ℝ) : ℂ) • A + ((b / (a + b) : ℝ) : ℂ) • B,
      isCPTP_combo _ _ (div_nonneg ha hpos.le) (div_nonneg hb hpos.le)
        (by field_simp) A B hA hB, ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      mul_div_cancel₀ _ h, mul_div_cancel₀ _ h]

/-! ### The decomposition -/

/-- The depolarizing-type channel eps R_sigma + (1-eps) id is CPTP. -/
theorem depolarizing_cptp {β : Type} [Fintype β] (σ : Mat β) (hσ : σ.PosSemidef)
    (hσ1 : Matrix.trace σ = 1) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (Λ : QMap β β)
    (hΛ : ∀ ρ, Λ ρ = (ε : ℂ) • (Matrix.trace ρ • σ) + (1 - (ε : ℂ)) • ρ) :
    IsCPTP Λ := by
  have h : Λ = (ε : ℂ) • (replaceQ σ : QMap β β) + ((1 - ε : ℝ) : ℂ) • LinearMap.id := by
    apply LinearMap.ext
    intro ρ
    rw [hΛ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, replaceQ_apply,
      LinearMap.id_apply]
    push_cast
    rfl
  rw [h]
  exact isCPTP_combo ε (1 - ε) hε0 (by linarith) (by ring) _ _
    (replaceQ_cptp σ hσ hσ1) isCPTP_id

/-- T11: the N-fold tensor power of eps R_sigma + (1-eps) id is eps^N times the
replacement by the product state sigma^{⊗N} plus (1-eps^N) times a channel. Here N is
the number of factors of the register Fin N → β, not the paper's qubits per site:
for WS, β is one site (dimension 2^N in the paper's notation), σ = I/2^N and the Lean
N is the number of sites; for Q, β = Fin 2, σ = I/2 and the Lean N is the number of
wires. The paper's composition over sites of D_{eps,x} ⊗ id is this tensor power,
because the factors are disjoint (up to a reindexing channel). -/
theorem depolarizing_tensorPower {β : Type} [Fintype β] [DecidableEq β]
    (σ : Mat β) (hσ : σ.PosSemidef) (hσ1 : Matrix.trace σ = 1) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (Λ : QMap β β)
    (hΛ : ∀ ρ, Λ ρ = (ε : ℂ) • (Matrix.trace ρ • σ) + (1 - (ε : ℂ)) • ρ) (N : ℕ) :
    ∃ (ω : Mat (Fin N → β)) (Φ : QMap (Fin N → β) (Fin N → β)),
      ω.PosSemidef ∧ Matrix.trace ω = 1 ∧ (∀ u v : Fin N → β, ω u v = ∏ j, σ (u j) (v j)) ∧
      IsCPTP Φ ∧
      tensorPowerQ Λ N = ((ε ^ N : ℝ) : ℂ) • (replaceQ ω) + ((1 - ε ^ N : ℝ) : ℂ) • Φ := by
  have hΛc := depolarizing_cptp σ hσ hσ1 ε hε0 hε1 Λ hΛ
  have hΛeq : Λ = (ε : ℂ) • (replaceQ σ : QMap β β) + ((1 - ε : ℝ) : ℂ) • LinearMap.id := by
    apply LinearMap.ext
    intro ρ
    rw [hΛ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, replaceQ_apply,
      LinearMap.id_apply]
    push_cast
    rfl
  induction N with
  | zero =>
    refine ⟨1, LinearMap.id, Matrix.PosSemidef.one, ?_, ?_, isCPTP_id, ?_⟩
    · rw [Matrix.trace_one, Fintype.card_unique, Nat.cast_one]
    · intro u v
      have hu : u = v := Subsingleton.elim u v
      subst hu
      simp
    · apply LinearMap.ext
      intro ρ
      ext u v
      have hu : u = v := Subsingleton.elim u v
      subst hu
      simp [tensorPowerQ, reindexQ, replaceQ_apply, Matrix.trace]
  | succ N ih =>
    obtain ⟨ω, Φ, hω, hω1, hωprod, hΦ, hdec⟩ := ih
    have hR := replaceQ_cptp (α := β) σ hσ hσ1
    obtain ⟨Ψ, hΨ, hΨeq⟩ := exists_cptp_combo (ε * (1 - ε ^ N)) (1 - ε)
      (mul_nonneg hε0 (by linarith [pow_le_one₀ hε0 hε1 (n := N)])) (by linarith)
      (tensorQ (replaceQ σ) Φ) (tensorQ LinearMap.id (tensorPowerQ Λ N))
      (tensorQ_cptp _ _ hR hΦ) (tensorQ_cptp _ _ isCPTP_id (tensorPowerQ_cptp Λ hΛc N))
    have hmid : tensorQ Λ (tensorPowerQ Λ N) =
        ((ε ^ (N + 1) : ℝ) : ℂ) • replaceQ (σ ⊗ₖ ω) +
          ((1 - ε ^ (N + 1) : ℝ) : ℂ) • Ψ := by
      have hw : ε * (1 - ε ^ N) + (1 - ε) = 1 - ε ^ (N + 1) := by ring
      rw [← hw, ← hΨeq]
      have h1 : tensorQ Λ (tensorPowerQ Λ N) = tensorQ ((ε : ℂ) • (replaceQ σ : QMap β β) +
          ((1 - ε : ℝ) : ℂ) • LinearMap.id) (tensorPowerQ Λ N) :=
        congrArg (fun X => tensorQ X (tensorPowerQ Λ N)) hΛeq
      have h2 : tensorQ (replaceQ σ : QMap β β) (tensorPowerQ Λ N) =
          ((ε ^ N : ℝ) : ℂ) • replaceQ (σ ⊗ₖ ω) +
            ((1 - ε ^ N : ℝ) : ℂ) • tensorQ (replaceQ σ : QMap β β) Φ := by
        rw [hdec, tensorQ_add_right, tensorQ_smul_right, tensorQ_smul_right, tensorQ_replaceQ]
      rw [h1, tensorQ_add_left, tensorQ_smul_left, tensorQ_smul_left, h2, smul_add, smul_smul,
        smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        show ε * ε ^ N = ε ^ (N + 1) by ring]
      abel
    refine ⟨reindexQ (tupleSplit N β).symm (σ ⊗ₖ ω),
      (reindexQ (tupleSplit N β).symm).comp (Ψ.comp (reindexQ (tupleSplit N β))),
      (hσ.kronecker hω).submatrix _, ?_, ?_, ?_, ?_⟩
    · rw [(reindexQ_cptp _).1, Matrix.trace_kronecker, hσ1, hω1, mul_one]
    · intro u v
      rw [Fin.prod_univ_succ]
      simp [reindexQ, tupleSplit, Fin.consEquiv, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, hωprod, Fin.tail]
    · exact (reindexQ_cptp _).comp (hΨ.comp (reindexQ_cptp _))
    · change (reindexQ (tupleSplit N β).symm).comp
        ((tensorQ Λ (tensorPowerQ Λ N)).comp (reindexQ (tupleSplit N β))) = _
      rw [hmid, LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp,
        LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_smul]
      congr 2
      apply LinearMap.ext
      intro ρ
      rw [LinearMap.comp_apply, LinearMap.comp_apply, replaceQ_apply, replaceQ_apply,
        map_smul, (reindexQ_cptp _).1]

/-- A replacement absorbs any preceding trace-preserving map. -/
theorem replaceQ_comp_tp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (σ : Mat γ) (G : QMap α β) (hG : ∀ ρ, Matrix.trace (G ρ) = Matrix.trace ρ) :
    (replaceQ σ : QMap β γ).comp G = replaceQ σ := by
  apply LinearMap.ext
  intro ρ
  rw [LinearMap.comp_apply, replaceQ_apply, replaceQ_apply, hG]

/-- The product state σ^{⊗N} on the register Fin N → β. -/
noncomputable def prodState {β : Type} (σ : Mat β) (N : ℕ) : Mat (Fin N → β) :=
  fun u v => ∏ j, σ (u j) (v j)

/-- A noisy layer (a CPTP gate layer G followed by the depolarizing-type noise on
every one of the N factors, rate eps) is the full replacement by σ^{⊗N} with weight
eps^N and otherwise a channel: the layer hypothesis hΛ of `replacement_ceiling` with
q = eps^N. -/
theorem noise_layer_replacement {β : Type} [Fintype β] [DecidableEq β]
    (σ : Mat β) (hσ : σ.PosSemidef) (hσ1 : Matrix.trace σ = 1) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (Λ : QMap β β)
    (hΛ : ∀ ρ, Λ ρ = (ε : ℂ) • (Matrix.trace ρ • σ) + (1 - (ε : ℂ)) • ρ) (N : ℕ)
    (G : QMap (Fin N → β) (Fin N → β)) (hG : IsCPTP G) :
    ∃ Φ : QMap (Fin N → β) (Fin N → β), IsCPTP Φ ∧
      ∀ ρ, (tensorPowerQ Λ N).comp G ρ =
        ((ε ^ N : ℝ) : ℂ) • (Matrix.trace ρ • prodState σ N) +
          (1 - ((ε ^ N : ℝ) : ℂ)) • Φ ρ := by
  obtain ⟨ω, Φ, _, _, hωprod, hΦ, hdec⟩ := depolarizing_tensorPower σ hσ hσ1 ε hε0 hε1 Λ hΛ N
  have hω : ω = prodState σ N := by
    ext u v
    exact hωprod u v
  refine ⟨Φ.comp G, hΦ.comp hG, ?_⟩
  intro ρ
  rw [LinearMap.comp_apply, hdec, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, replaceQ_apply, hG.1, LinearMap.comp_apply, ← hω]
  push_cast
  rfl

/-- The ceiling for a circuit of noisy layers (Sections 10 and 18, WS and Q): each
layer is a CPTP gate layer G_i followed by noise of rate eps on every one of the N
factors; with eps0 ≤ eps, after t layers every encoder and decoder has fidelity at
most 1/4 + (3/4)(1 - eps0^N)^t. -/
theorem noisy_circuit_ceiling {β : Type} [Fintype β] [DecidableEq β] (σ : Mat β)
    (hσ : σ.PosSemidef) (hσ1 : Matrix.trace σ = 1) (ε ε0 : ℝ) (h0 : 0 ≤ ε0) (h01 : ε0 ≤ ε)
    (hε1 : ε ≤ 1) (Λ : QMap β β)
    (hΛ : ∀ ρ, Λ ρ = (ε : ℂ) • (Matrix.trace ρ • σ) + (1 - (ε : ℂ)) • ρ) (N : ℕ)
    (G : ℕ → QMap (Fin N → β) (Fin N → β)) (hG : ∀ i, IsCPTP (G i))
    (Γ : ℕ → QMap (Fin N → β) (Fin N → β)) (hΓ0 : Γ 0 = LinearMap.id)
    (hΓ : ∀ i, Γ (i + 1) = ((tensorPowerQ Λ N).comp (G i)).comp (Γ i)) (t : ℕ)
    (E : QMap (Fin 2) (Fin N → β)) (hE : IsCPTP E)
    (D : QMap (Fin N → β) (Fin 2)) (hD : IsCPTP D) :
    entanglementFidelity E (Γ t) D ≤ 1 / 4 + 3 / 4 * (1 - ε0 ^ N) ^ t := by
  choose Φ hΦ hdec using fun i =>
    noise_layer_replacement σ hσ hσ1 ε (h0.trans h01) hε1 Λ hΛ N (G i) (hG i)
  have hω1 : Matrix.trace (prodState σ N) = 1 := by
    obtain ⟨ω, _, _, hω1, hωprod, _, _⟩ :=
      depolarizing_tensorPower σ hσ hσ1 ε (h0.trans h01) hε1 Λ hΛ N
    have hω : ω = prodState σ N := by
      ext u v
      exact hωprod u v
    rw [← hω, hω1]
  exact replacement_ceiling (ε0 ^ N) t (fun i => (tensorPowerQ Λ N).comp (G i))
    (fun _ => ε ^ N) (fun _ => prodState σ N) Φ
    (fun _ => ⟨pow_le_pow_left₀ h0 h01 N, pow_le_one₀ (h0.trans h01) hε1⟩)
    (fun _ => hω1) hΦ (fun i ρ => hdec i ρ) Γ hΓ0 hΓ E hE D hD

end QuantumScope
