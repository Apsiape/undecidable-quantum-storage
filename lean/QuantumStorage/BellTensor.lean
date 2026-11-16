import QuantumStorage.BellMarginal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace QuantumScope

/-- Amplification over any finite basis, using the frozen block formula. -/
noncomputable def amplifyAnyQ (ι : Type) {α β : Type}
    [Fintype ι] [Fintype α] [Fintype β] (T : QMap α β) :
    QMap (ι × α) (ι × β) where
  toFun ρ u v := T (fun x y => ρ (u.1, x) (v.1, y)) u.2 v.2
  map_add' ρ σ := by
    ext u v
    change T ((fun x y => ρ (u.1, x) (v.1, y)) +
      (fun x y => σ (u.1, x) (v.1, y))) u.2 v.2 = _
    rw [map_add]; rfl
  map_smul' c ρ := by
    ext u v
    change T (c • (fun x y => ρ (u.1, x) (v.1, y))) u.2 v.2 = _
    rw [map_smul]; rfl

theorem amplifyAnyQ_posSemidef {ι α β : Type}
    [Fintype ι] [Fintype α] [Fintype β] (T : QMap α β) (hT : IsCPTP T)
    (ρ : Mat (ι × α)) (hρ : ρ.PosSemidef) :
    (amplifyAnyQ ι T ρ).PosSemidef := by
  let e := Fintype.equivFin ι
  have h := hT.2 (Fintype.card ι)
    (ρ.submatrix (fun x : Fin (Fintype.card ι) × α => (e.symm x.1, x.2))
      (fun x : Fin (Fintype.card ι) × α => (e.symm x.1, x.2)))
    (hρ.submatrix _)
  have hh := h.submatrix (fun x : ι × β => (e x.1, x.2))
  change Matrix.PosSemidef (fun u v : ι × β => T (fun x y =>
    ρ (e.symm (e u.1), x) (e.symm (e v.1), y)) u.2 v.2) at hh
  change Matrix.PosSemidef (fun u v : ι × β =>
    T (fun x y => ρ (u.1, x) (v.1, y)) u.2 v.2)
  simpa only [Equiv.symm_apply_apply] using hh

theorem amplifyAnyQ_trace {ι α β : Type}
    [Fintype ι] [Fintype α] [Fintype β] (T : QMap α β)
    (hT : ∀ ρ, Matrix.trace (T ρ) = Matrix.trace ρ) (ρ : Mat (ι × α)) :
    Matrix.trace (amplifyAnyQ ι T ρ) = Matrix.trace ρ := by
  calc
    Matrix.trace (amplifyAnyQ ι T ρ) =
        ∑ i : ι, Matrix.trace (T (fun x y => ρ (i, x) (i, y))) := by
      simp [Matrix.trace, Matrix.diag, amplifyAnyQ, Fintype.sum_prod_type]
    _ = ∑ i : ι, Matrix.trace (fun x y => ρ (i, x) (i, y)) := by simp_rw [hT]
    _ = Matrix.trace ρ := by simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

theorem amplifyAnyQ_cptp {ι α β : Type}
    [Fintype ι] [Fintype α] [Fintype β] (T : QMap α β) (hT : IsCPTP T) :
    IsCPTP (amplifyAnyQ ι T) := by
  constructor
  · exact amplifyAnyQ_trace T hT.1
  · intro r ρ hρ
    let e : ((Fin r × ι) × α) ≃ (Fin r × (ι × α)) := Equiv.prodAssoc _ _ _
    have h := amplifyAnyQ_posSemidef T hT
      (ρ.submatrix e e) (hρ.submatrix e)
    have hh := h.submatrix (Equiv.prodAssoc (Fin r) ι β).symm
    exact hh

/-- Apply a channel to the first factor and leave the second factor intact. -/
noncomputable def firstQ {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (T : QMap α β) : QMap (α × γ) (β × γ) :=
  (reindexQ (Equiv.prodComm γ β)).comp
    ((amplifyAnyQ γ T).comp (reindexQ (Equiv.prodComm α γ)))

theorem firstQ_apply {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (T : QMap α β) (ρ : Mat (α × γ)) (x y : β × γ) :
    firstQ T ρ x y = T (fun a b => ρ (a, x.2) (b, y.2)) x.1 y.1 := rfl

theorem firstQ_cptp {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (T : QMap α β) (hT : IsCPTP T) : IsCPTP (firstQ (γ := γ) T) :=
  (reindexQ_cptp _).comp ((amplifyAnyQ_cptp T hT).comp (reindexQ_cptp _))

/-- Independent application of two finite-dimensional channels. -/
noncomputable def tensorQ {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (T : QMap α β) (U : QMap γ δ) : QMap (α × γ) (β × δ) :=
  (firstQ T).comp (amplifyAnyQ α U)

theorem tensorQ_cptp {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (T : QMap α β) (U : QMap γ δ) (hT : IsCPTP T) (hU : IsCPTP U) :
    IsCPTP (tensorQ T U) := (firstQ_cptp T hT).comp (amplifyAnyQ_cptp U hU)

theorem partialTraceRight_firstQ {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (T : QMap α β) (ρ : Mat (α × γ)) :
    partialTraceRight (firstQ T ρ) = T (partialTraceRight ρ) := by
  have h : partialTraceRight ρ = ∑ z : γ, (fun a b => ρ (a, z) (b, z)) := by
    ext a b; simp [partialTraceRight, Matrix.sum_apply]
  rw [h, map_sum]
  ext x y
  simp [partialTraceRight, firstQ_apply, Matrix.sum_apply]

theorem partialTraceRight_amplifyAnyQ {α γ δ : Type}
    [Fintype α] [Fintype γ] [Fintype δ]
    (U : QMap γ δ) (hU : ∀ ρ, Matrix.trace (U ρ) = Matrix.trace ρ)
    (ρ : Mat (α × γ)) :
    partialTraceRight (amplifyAnyQ α U ρ) = partialTraceRight ρ := by
  ext x y
  exact hU (fun a b => ρ (x, a) (y, b))

theorem partialTraceRight_tensorQ {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (T : QMap α β) (U : QMap γ δ)
    (hU : ∀ ρ, Matrix.trace (U ρ) = Matrix.trace ρ) (ρ : Mat (α × γ)) :
    partialTraceRight (tensorQ T U ρ) = T (partialTraceRight ρ) := by
  change partialTraceRight (firstQ T (amplifyAnyQ α U ρ)) = _
  rw [partialTraceRight_firstQ, partialTraceRight_amplifyAnyQ U hU]

end QuantumScope
