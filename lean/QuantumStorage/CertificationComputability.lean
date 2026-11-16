import QuantumStorage.Definitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CertificationScope

/-- A computable exact test supplies a single universal natural quantifier. -/
theorem certificate_pi01 (d : Data) : IsPi01 (RationalCertificate d) := by
  let dec : ℕ → ℕ × (ℕ × ℕ) := fun s => (s.unpair.1, s.unpair.2.unpair)
  have hd : Computable dec :=
    (Computable.fst.comp Computable.unpair).pair
      (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hr : Computable (fun z : ℕ × ℕ => d.test (z.1, dec z.2)) :=
    d.test_computable.comp (Computable.fst.pair (hd.comp Computable.snd))
  refine ⟨fun z => d.test (z.1, dec z.2), hr, ?_⟩
  intro n
  constructor
  · intro h s
    apply (d.test_spec n _ _ _).2
    rintro ⟨hL, ht, hlo, hhi⟩
    exact h _ _ _ hL ht hlo hhi
  · intro h L t q hL ht hlo hhi
    obtain ⟨k, rfl⟩ := d.rate_surjective q
    have hh : d.test (n, L, t, k) = true := by
      simpa [dec] using h (Nat.pair L (Nat.pair t k))
    exact (d.test_spec n L t k).1 hh ⟨hL, ht, hlo, hhi⟩

/-- The supplied compiler makes nonhalting hard for every computable
universal Boolean predicate. The search is explicitly partial recursive. -/
theorem nonhalting_hard (u : UniversalInput) (Q : ℕ → Prop) (hQ : IsPi01 Q) :
    ManyOneReducible Q (fun n => ¬ (u.run n).Dom) := by
  classical
  obtain ⟨R, hR, hQ⟩ := hQ
  let search : ℕ →. ℕ := fun n => Nat.rfind fun s => Part.some (!(R (n, s)))
  have hs : Partrec search :=
    Partrec.rfind (Primrec.not.to_comp.comp hR).partrec.to₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hs)
  let specialize : ℕ → Nat.Partrec.Code := fun n =>
    Nat.Partrec.Code.comp c (Nat.Partrec.Code.const n)
  have hspec : Computable specialize :=
    Nat.Partrec.Code.primrec₂_comp.to_comp.comp (Computable.const c)
      Nat.Partrec.Code.primrec_const.to_comp
  have heval (n : ℕ) : (specialize n).eval 0 = search n := by
    simp only [specialize, Nat.Partrec.Code.eval, Nat.Partrec.Code.eval_const, Part.bind_eq_bind, Part.bind_some]
    exact congrFun hc n
  have hdom (n : ℕ) : (search n).Dom ↔ ∃ s, R (n, s) = false := by
    change (Nat.rfind (fun s => Part.some (!(R (n, s))))).Dom ↔ _
    rw [Nat.rfind_dom]
    simp
  refine ⟨fun n => u.compile (specialize n), u.compile_computable.comp hspec, ?_⟩
  intro n
  change Q n ↔ ¬ (u.run (u.compile (specialize n))).Dom
  rw [u.compile_spec, heval, hdom, hQ n]
  simp

/-- A computable complement of this nonhalting set would decide the
Mathlib halting problem through the explicit input compiler. -/
theorem nonhalting_not_computable (u : UniversalInput) :
    ¬ ComputablePred (fun n => ¬ (u.run n).Dom) := by
  classical
  intro h
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_of_manyOneReducible
    (q := fun n => ¬ ¬ (u.run n).Dom) _ h.not
  refine ⟨u.compile, u.compile_computable, ?_⟩
  intro e
  simp only [not_not, u.compile_spec]

end CertificationScope
