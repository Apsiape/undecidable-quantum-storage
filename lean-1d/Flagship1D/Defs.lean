import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lean core for the one-dimensional sparsity estimates: definitions and statements

Papers: R. Douglas, N. Mghirbi, *An uncomputable noise diagram on the line and a
finite-energy Gibbs diagram on the square lattice*, version 2.0.0 (below: the classical
construction), and Lemma 12.1 of the quantum storage paper, version 3.0.

This file holds every definition and every statement (as a named `Prop`). `Challenge.lean`
is a copy of it followed by `theorem name : Statement := sorry` lines (comparator
format); the proof files (`Stage1.lean`, `Stage2.lean`, `Stage3.lean`) prove each
statement, and `Solution.lean` imports them. Page references are to the cited versions.

Conventions.
* The site--time lattice is `ℤ × ℤ` (first coordinate: site, second: time).
* `V^j = [0, P^j) × [0, T^j)`, so a translate of `c·V^j` is
  `box a b (c * P ^ j) (c * T ^ j)`; all rectangles are half-open.
-/

namespace Flagship1D

open MeasureTheory ProbabilityTheory

/-! ## 1. Rectangles and sparsity (Section 4.1) -/

/-- The half-open lattice rectangle `[a, a + L) × [b, b + M)` in `ℤ × ℤ`. -/
def box (a b : ℤ) (L M : ℕ) : Set (ℤ × ℤ) :=
  {z | a ≤ z.1 ∧ z.1 < a + (L : ℤ) ∧ b ≤ z.2 ∧ z.2 < b + (M : ℤ)}

/-- **Definition 4.1 (Sparsity)** of the classical construction, p. 9.
"A set is 0-sparse if it is empty. It is j-sparse if every translate Q of wV^j
admits a translate J of 3wV^{j-1} such that (E ∩ Q) \ J is (j-1)-sparse." -/
def Sparse (P T w : ℕ) : ℕ → Set (ℤ × ℤ) → Prop
  | 0, E => E = ∅
  | j + 1, E => ∀ a b : ℤ, ∃ c d : ℤ,
      Sparse P T w j ((E ∩ box a b (w * P ^ (j + 1)) (w * T ^ (j + 1))) \
        box c d (3 * w * P ^ j) (3 * w * T ^ j))

/-- p. 9, after Definition 4.1: "Sparsity is inherited by subsets". -/
def SparseInheritedBySubsets : Prop :=
  ∀ (P T w j : ℕ) (E F : Set (ℤ × ℤ)), F ⊆ E → Sparse P T w j E → Sparse P T w j F

/-- p. 9, after Definition 4.1: "(j-1)-sparsity implies j-sparsity". -/
def SparseImpliesNextSparse : Prop :=
  ∀ (P T w j : ℕ) (E : Set (ℤ × ℤ)), Sparse P T w j E → Sparse P T w (j + 1) E

/-- p. 9, after Definition 4.1: "A full V^j is never j-sparse."
Stated under `w ≥ 1`, `T ≥ 1` and `P ≥ 3w + 2` (the paper has `P = 5·2^w`), which is
what makes "a deletion of 3wV^{j-1} cannot intersect two widely separated full
V^{j-1} rectangles" true. -/
def FullBoxNotSparse : Prop :=
  ∀ (P T w : ℕ), 1 ≤ w → 3 * w + 2 ≤ P → 1 ≤ T →
    ∀ (j : ℕ) (a b : ℤ), ¬ Sparse P T w j (box a b (P ^ j) (T ^ j))

/-! ## 2. Lemma 4.2 (Disjoint sparse-set witnesses), p. 10 -/

/-- Grid indices of the deterministic child list: positions `k·wP^j` (and `l·wT^j`)
for `0 ≤ k ≤ 2P - 2` (`0 ≤ l ≤ 2T - 2`); the last position is flush with the far
boundary of the parent, since `2wP^{j+1} = 2P·wP^j`. -/
def childIndex (P T : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (2 * P - 1) ×ˢ Finset.range (2 * T - 1)

/-- The full child box of side vector `2wV^j` with grid index `kl`, inside the parent
box of side vector `2wV^{j+1}` with lower corner `(a, b)`. -/
def childBox (P T w j : ℕ) (a b : ℤ) (kl : ℕ × ℕ) : Set (ℤ × ℤ) :=
  box (a + ((kl.1 * (w * P ^ j) : ℕ) : ℤ)) (b + ((kl.2 * (w * T ^ j) : ℕ) : ℤ))
    (2 * w * P ^ j) (2 * w * T ^ j)

/-- **Lemma 4.2, deterministic part.** "If the restriction to a full box of side vector
2wV^{j+1} fails (j+1)-sparsity, two disjoint full child boxes of side vector 2wV^j
inside it fail j-sparsity. The child positions come from a deterministic list of at
most (2P+3)(2T+3) boxes."
(The probabilistic "Consequently ..." sentence is not part of this statement; its
recursion is `BjRecursion` below.) -/
def Lemma_4_2_Witness : Prop :=
  ∀ (P T w j : ℕ) (a b : ℤ),
    (childIndex P T).card ≤ (2 * P + 3) * (2 * T + 3) ∧
    (∀ kl ∈ childIndex P T,
      childBox P T w j a b kl ⊆ box a b (2 * w * P ^ (j + 1)) (2 * w * T ^ (j + 1))) ∧
    ∀ E : Set (ℤ × ℤ),
      ¬ Sparse P T w (j + 1) (E ∩ box a b (2 * w * P ^ (j + 1)) (2 * w * T ^ (j + 1))) →
      ∃ kl ∈ childIndex P T, ∃ kl' ∈ childIndex P T,
        Disjoint (childBox P T w j a b kl) (childBox P T w j a b kl') ∧
        ¬ Sparse P T w j (E ∩ childBox P T w j a b kl) ∧
        ¬ Sparse P T w j (E ∩ childBox P T w j a b kl')

/-- Proof of Lemma 4.2, p. 10: "there are at most D = 8(P+2)^2(T+2)^2 candidate pairs"
(unordered pairs from a list of at most (2P+3)(2T+3) candidates). -/
def Lemma_4_2_PairCount : Prop :=
  ∀ P T n : ℕ, n ≤ (2 * P + 3) * (2 * T + 3) → n.choose 2 ≤ 8 * (P + 2) ^ 2 * (T + 2) ^ 2

/-- Proof of Lemma 4.2, p. 10: "At rank zero b_0 ≤ 4w^2 u ... Thus b_{j+1} ≤ D b_j^2, and
b_j ≤ D^{-1}(4Dw^2u)^{2^j} ≤ D^{-1}u^{2^{j-1}} if u ≤ (4Dw^2)^{-2}."
Here `b` is any nonnegative sequence obeying the two displayed recursive bounds. -/
def BjRecursion : Prop :=
  ∀ (D u w : ℝ) (b : ℕ → ℝ), 0 < D → 0 ≤ u → (∀ j, 0 ≤ b j) →
    b 0 ≤ 4 * w ^ 2 * u → (∀ j, b (j + 1) ≤ D * b j ^ 2) →
    ∀ j : ℕ, b j ≤ D⁻¹ * (4 * D * w ^ 2 * u) ^ (2 ^ j) ∧
      (u ≤ ((4 * D * w ^ 2) ^ 2)⁻¹ → b j ≤ D⁻¹ * u ^ ((2 : ℝ) ^ ((j : ℝ) - 1)))

/-! ## 3. Selection of an independent subfamily (Section 4.4, proof of Lemma 4.6) -/

/-- p. 15, proof of Lemma 4.6: "the intersection graph of the enlarged leaves has degree
at most a fixed Δ_leaf ... Select at least L/(Δ_leaf + 1) disjoint supports in each
deterministic tree."
Abstract form: a finite family `s` with a symmetric conflict relation of degree at most
`D` (each member conflicts with at most `D` others, all of which lie in some finite set
of size `≤ D`) contains a conflict-free subfamily `t` with `|s| ≤ (D + 1)|t|`. -/
def IndependentSelection : Prop :=
  ∀ {α : Type} [DecidableEq α] (s : Finset α) (adj : α → α → Prop) (D : ℕ),
    (∀ x y, adj x y → adj y x) →
    (∀ x ∈ s, ∃ N : Finset α, N.card ≤ D ∧ ∀ y ∈ s, y ≠ x → adj x y → y ∈ N) →
    ∃ t ⊆ s, s.card ≤ (D + 1) * t.card ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ adj x y

/-! ## 4. Independence on disjoint supports and the tree bound (Lemma 4.6, eq. (4)) -/

/-- Independent flags (one σ-algebra `m x` per site, `iIndep`); an event is
"measurable in" a support `S` if it is measurable for `⨆ x ∈ S, m x`.
p. 10 (proof of Lemma 4.2): "Disjoint children carry independent flags";
p. 14 (Section 4.4): "products concern disjoint innovation supports".
Statement: for events on pairwise disjoint supports, the probability of the
intersection is the product of the probabilities. -/
def ProductOnDisjointSupports : Prop :=
  ∀ {Ω X ι : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : X → MeasurableSpace Ω), (∀ x, m x ≤ mΩ) → iIndep m μ →
    ∀ (S : ι → Set X) (A : ι → Set Ω), (∀ ℓ, MeasurableSet[⨆ x ∈ S ℓ, m x] (A ℓ)) →
    ∀ sel : Finset ι, (∀ ℓ ∈ sel, ∀ ℓ' ∈ sel, ℓ ≠ ℓ' → Disjoint (S ℓ) (S ℓ')) →
      μ (⋂ ℓ ∈ sel, A ℓ) = ∏ ℓ ∈ sel, μ (A ℓ)

/-- **Lemma 4.6, eq. (4)**, p. 15. "There are at most C^{L-1} possible trees for
fixed root. If each leaf event is measurable in a bounded enlargement of its leaf, the
intersection graph of the enlarged leaves has degree at most a fixed Δ_leaf ... Select at
least L/(Δ_leaf+1) disjoint supports in each deterministic tree. If the leaf probability is
at most α, the product bound on the selected supports followed by a union over trees is at
most (C α^{1/(Δ_leaf+1)})^{2^{i-j}}."
Abstract form: a tree is represented by its set of `L` leaves (`L = 2^{i-j}` in the paper);
`S ℓ` is the enlarged leaf (support) and `A ℓ` the leaf event. -/
def TreeBound : Prop :=
  ∀ {Ω X ι : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : X → MeasurableSpace Ω), (∀ x, m x ≤ mΩ) → iIndep m μ →
    ∀ (S : ι → Set X) (A : ι → Set Ω), (∀ ℓ, MeasurableSet[⨆ x ∈ S ℓ, m x] (A ℓ)) →
    ∀ (α C : ℝ) (Δ L : ℕ), 0 ≤ α → α ≤ 1 → 1 ≤ C → (∀ ℓ, μ (A ℓ) ≤ ENNReal.ofReal α) →
    ∀ trees : Finset (Finset ι), (trees.card : ℝ) ≤ C ^ (L - 1) →
      (∀ t ∈ trees, t.card = L) →
      (∀ t ∈ trees, ∀ ℓ ∈ t, ∃ N : Finset ι, N.card ≤ Δ ∧
          ∀ ℓ' ∈ t, ℓ' ≠ ℓ → ¬ Disjoint (S ℓ) (S ℓ') → ℓ' ∈ N) →
      μ (⋃ t ∈ trees, ⋂ ℓ ∈ t, A ℓ) ≤ ENNReal.ofReal ((C * α ^ (1 / ((Δ : ℝ) + 1))) ^ L)

/-! ## 5. Numerical choices (Appendix A and the organization proofs)

Parameters from p. 5 and the constants table (Appendix A, p. 83). -/

namespace Params

/-- `q = w^2`. -/
def q (w : ℕ) : ℕ := w ^ 2
/-- `A = w^3`. -/
def A (w : ℕ) : ℕ := w ^ 3
/-- `B = 128q`. -/
def B (w : ℕ) : ℕ := 128 * q w
/-- `v = w^4`. -/
def v (w : ℕ) : ℕ := w ^ 4
/-- `P_0 = 2^w`. -/
def P0 (w : ℕ) : ℕ := 2 ^ w
/-- `P = 5 P_0`. -/
def P (w : ℕ) : ℕ := 5 * P0 w
/-- `H_0 = 2q + 2` (the handle). -/
def H0 (w : ℕ) : ℕ := 2 * q w + 2
/-- `d_0 = (2A + 4) H_0` (Main cycle). -/
def d0 (w : ℕ) : ℕ := (2 * A w + 4) * H0 w
/-- `d_1 = q d_0` (active Shrink spacing). -/
def d1 (w : ℕ) : ℕ := q w * d0 w
/-- `m = ⌊w/5⌋`. -/
def m (w : ℕ) : ℕ := w / 5
/-- `d = 4w + 8`. -/
def d (w : ℕ) : ℕ := 4 * w + 8
/-- `M = 128 d` (verifier epoch parameter). -/
def M (w : ℕ) : ℕ := 128 * d w
/-- `Δ = 1024 q` (ordinary depth margin). -/
def Delta (w : ℕ) : ℕ := 1024 * q w
/-- `t_c = 2d + 9q + 40` (clearance time, Lemma 5.7). -/
def tc (w : ℕ) : ℕ := 2 * d w + 9 * q w + 40
/-- `N = 200 A d_1` (uniform search allowance). -/
def N (w : ℕ) : ℕ := 200 * A w * d1 w
/-- `D_tr = 50A d_1 + (6N + 4w^6 + 21)(5d_0 + 1) + w^6 + 2d_0 + 20` (Lemma 5.10, p. 39). -/
def Dtr (w : ℕ) : ℕ :=
  50 * A w * d1 w + (6 * N w + 4 * w ^ 6 + 21) * (5 * d0 w + 1) + w ^ 6 + 2 * d0 w + 20

end Params

open Params

/-- Lemma 5.7, p. 29, and Lemma 5.8, p. 34:
"2(B-20)-(B+30q+40)=98q-80>0" (global choice `w ≥ 10^10`). -/
def Num_CavityGain : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w →
    2 * ((B w : ℤ) - 20) - ((B w : ℤ) + 30 * q w + 40) = 98 * (q w : ℤ) - 80 ∧
    (0 : ℤ) < 98 * (q w : ℤ) - 80

/-- Lemma 5.6, p. 24: "Since q+d+32<B" (global choice `w ≥ 10^10`). -/
def Num_FlankPass : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → q w + d w + 32 < B w

/-- Lemma 5.6, p. 25: "All response dates fit d+4q+14+2d_0<w^6"
(global choice `w ≥ 10^10`). -/
def Num_FlankResponseTime : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → d w + 4 * q w + 14 + 2 * d0 w < w ^ 6

/-- Lemma 5.7, p. 27: "Put t_c=2d+9q+40 ... note that t_c<5H_0 for
w≥100000". -/
def Num_ClearanceTime : Prop :=
  ∀ w : ℕ, 100000 ≤ w → tc w < 5 * H0 w

/-- Lemma 5.7, p. 27: "in less than 2d_0+10H_0 after J. This is <w^6 for
w≥100000"; also Lemma 5.8, p. 34: "<2d_0+10(2q+2)<w^6". -/
def Num_ResponseTime : Prop :=
  ∀ w : ℕ, 100000 ≤ w → 2 * d0 w + 10 * H0 w < w ^ 6

/-- Lemma 5.7, p. 28: "since q+2d+55≤30q+40" (global choice). -/
def Num_CavityLength : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → q w + 2 * d w + 55 ≤ 30 * q w + 40

/-- Lemma 5.8, p. 34, and Lemma 5.10, p. 40: "2B+40q+40<.2A"
(global choice `w ≥ 10^10`). -/
def Num_WoundBand : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → ((2 * B w + 40 * q w + 40 : ℕ) : ℚ) < 0.2 * (A w : ℚ)

/-- Lemma 5.9, p. 37: "At w≥100000, 3Δ/A=3072/w<0.031". -/
def Num_SeedRatio : Prop :=
  ∀ w : ℕ, 100000 ≤ w →
    (3 * Delta w : ℚ) / (A w : ℚ) = 3072 / (w : ℚ) ∧ (3072 : ℚ) / (w : ℚ) < 0.031

/-- Lemma 5.9, p. 37: "d_1=q(2A+4)(2q+2)>4w^7 implies w^6<d_1". -/
def Num_SeedSpacing : Prop :=
  ∀ w : ℕ, 100000 ≤ w →
    d1 w = q w * (2 * A w + 4) * (2 * q w + 2) ∧ 4 * w ^ 7 < d1 w ∧ w ^ 6 < d1 w

/-- Lemma 5.9, p. 37: with `L = 3A + 3Δ`, "Hence 8(L+2)+5<100A" (at
`w ≥ 100000`). -/
def Num_SeedCount : Prop :=
  ∀ w : ℕ, 100000 ≤ w → 8 * ((3 * A w + 3 * Delta w) + 2) + 5 < 100 * A w

/-- Lemma 5.10, p. 41: "Repeating epochs costs at most
(ceil((20A+2M)/(M-4d-1))+2)(M+1) ticks, bounded by 100A+4(M+1) since (M+1)/(M-4d-1)<2"
(global choice `w ≥ 10^10`). -/
def Num_EpochCost : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w →
    ((M w : ℚ) + 1) / ((M w : ℚ) - 4 * d w - 1) < 2 ∧
    (⌈((20 * A w + 2 * M w : ℕ) : ℚ) / ((M w : ℚ) - 4 * d w - 1)⌉₊ + 2) * (M w + 1) ≤
      100 * A w + 4 * (M w + 1)

/-- Lemma 5.10, p. 39: "choose w so that 2(D_tr+10A+10q)+d<P_0/2 and
12A+4q+D_tr+10A+10q<P_0/2" — verified at the global choice `w ≥ 10^10`. -/
def Num_TransportMargin : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w →
    ((2 * (Dtr w + 10 * A w + 10 * q w) + d w : ℕ) : ℚ) < (P0 w : ℚ) / 2 ∧
    ((12 * A w + 4 * q w + Dtr w + 10 * A w + 10 * q w : ℕ) : ℚ) < (P0 w : ℚ) / 2

/-- Proof of Lemma 5.4, localization paragraph, p. 19: "The rear-wall radius 3vd_0+2w^6+12d_0+20
... <P/10 for sufficiently large w" — proved as arithmetic at the global choice `w ≥ 10^10`. -/
def Num_RearWall : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w →
    ((3 * v w * d0 w + 2 * w ^ 6 + 12 * d0 w + 20 : ℕ) : ℚ) < (P w : ℚ) / 10

/-- Proof of Lemma 5.4, localization paragraph, p. 19: "fit within 19·2·16=608 owner widths
and 19·2·6=228 owner periods"; "608<m=⌊w/5⌋ at the global choice w≥10^10" (arithmetic only). -/
def Num_OwnerCollar : Prop :=
  19 * 2 * 16 = 608 ∧ 19 * 2 * 6 = 228 ∧ ∀ w : ℕ, 10 ^ 10 ≤ w → 608 < m w

/-- Proof of Lemma 5.4, localization paragraph, p. 20: "3w+2m+4+2·608<4w+8 for the chosen w";
Appendix A, p. 83: "Common span 3w+2m+4+2(608)<d" (arithmetic only). -/
def Num_CommonSpan : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → 3 * w + 2 * m w + 4 + 2 * 608 < d w

/-- Lemma 5.12, p. 47: "of width at most d+10<q" (global choice). -/
def Num_SatelliteWidth : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → d w + 10 < q w

/-- Lemma 5.16, p. 54: "Here C=2,000,000; if necessary enlarge w so
w>100(C+1000)" — already true at the global choice `w ≥ 10^10`. -/
def Num_DeficitConstant : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → 100 * (2000000 + 1000) < w

/-- Lemma 5.19, p. 58: "since 5q+2d+12<4(2q+2)" (global choice). -/
def Num_Recruitment : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → 5 * q w + 2 * d w + 12 < 4 * (2 * q w + 2)

/-- Lemma 5.23, p. 71: "D=d+4(q+20)<5q<B-10"; Appendix A, p. 83:
"Cost d+4(q+20)<5q" (global choice). -/
def Num_AdvanceDebit : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → d w + 4 * (q w + 20) < 5 * q w ∧ 5 * q w < B w - 10

/-- Appendix A, p. 83: "Final common exception has width at most d+q+42<2q" (global
choice). -/
def Num_EndpointException : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → d w + q w + 42 < 2 * q w

/-- Appendix A, p. 83: "also Δ<16B+2d+24<3Δ" (global choice). -/
def Num_EndGap : Prop :=
  ∀ w : ℕ, 10 ^ 10 ≤ w → Delta w < 16 * B w + 2 * d w + 24 ∧ 16 * B w + 2 * d w + 24 < 3 * Delta w

/-- p. 5 and Appendix A: the paper's `P = 5P_0 = 5·2^w` satisfies the hypothesis
`P ≥ 3w + 2` under which `FullBoxNotSparse` is stated (for every `w`). -/
def Num_FullBoxHypothesis : Prop :=
  ∀ w : ℕ, 3 * w + 2 ≤ P w

/-! ## 6. Restricted witness trees with dependent stencil flags

Sources: Lemma 12.1 of the quantum storage paper, version 3.0 ("restricted witness trees and
their probability"), and the classical construction, Lemma 4.2 (p. 10) and
Lemma 4.6 (p. 15). -/

/-- `D = 8(P+2)^2(T+2)^2`, the bound on unordered candidate pairs (classical construction,
p. 10; `D_R` in Lemma 12.1). -/
def Dpair (P T : ℕ) : ℕ := 8 * (P + 2) ^ 2 * (T + 2) ^ 2

/-- The native flag field of a stencil: `q` is flagged iff at least one key of the
finite stencil `sten q` is on (Lemma 12.1, "the indicator that at least one independent
elementary depolarization flag in a finite stencil Σ_R(q) is one"). -/
def stencilFlags {κ : Type} (sten : ℤ × ℤ → Finset κ) (ω : κ → Bool) : Set (ℤ × ℤ) :=
  {q | ∃ k ∈ sten q, ω k = true}

set_option linter.deprecated false in
/-- Independent keys: the product of Bernoulli laws on an arbitrary key set, key `k`
on with probability `p k` (unequal rates allowed). `PMF.bernoulli` is the pinned Mathlib's
Bernoulli law (deprecated there in favour of `bernoulliMeasure`, same law). -/
noncomputable def keyNoise {κ : Type} (p : κ → NNReal) (hp : ∀ k, p k ≤ 1) :
    Measure (κ → Bool) :=
  Measure.infinitePi (fun k => (PMF.bernoulli (p k) (hp k)).toMeasure)

/-- Unordered separated pairs of child indices of Lemma 4.2's list, each listed once
(lexicographically smaller index first). Separated means the two child boxes are
disjoint (indices at least two apart in some coordinate). -/
def sepPairs (P T : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (childIndex P T ×ˢ childIndex P T).filter (fun pr =>
    (pr.1.1 < pr.2.1 ∨ (pr.1.1 = pr.2.1 ∧ pr.1.2 < pr.2.2)) ∧
    (pr.1.1 + 2 ≤ pr.2.1 ∨ pr.2.1 + 2 ≤ pr.1.1 ∨ pr.1.2 + 2 ≤ pr.2.2 ∨ pr.2.2 + 2 ≤ pr.1.2))

/-- The deterministic family of witness trees of depth `r` from a fixed root: each tree is
represented by the set of its root-to-leaf paths (lists of child indices); an internal
node chooses one separated pair. -/
def witnessTrees (P T : ℕ) : ℕ → Finset (Finset (List (ℕ × ℕ)))
  | 0 => {{[]}}
  | r + 1 => (sepPairs P T).biUnion (fun pr =>
      (witnessTrees P T r ×ˢ witnessTrees P T r).image
        (fun tt => tt.1.image (List.cons pr.1) ∪ tt.2.image (List.cons pr.2)))

/-- The region of the node reached by a path from a root box of rank `m + r` with lower
corner `(a, b)`: its own doubled box intersected with the boxes of all its ancestors
(leaves have rank `m`). -/
def treeRegion (P T w m : ℕ) : ℕ → ℤ → ℤ → List (ℕ × ℕ) → Set (ℤ × ℤ)
  | 0, a, b, _ => box a b (2 * w * P ^ m) (2 * w * T ^ m)
  | r + 1, a, b, [] => box a b (2 * w * P ^ (m + r + 1)) (2 * w * T ^ (m + r + 1))
  | r + 1, a, b, kl :: p => box a b (2 * w * P ^ (m + r + 1)) (2 * w * T ^ (m + r + 1)) ∩
      treeRegion P T w m r (a + ((kl.1 * (w * P ^ (m + r)) : ℕ) : ℤ))
        (b + ((kl.2 * (w * T ^ (m + r)) : ℕ) : ℤ)) p

/-- The lower corner of the box reached by a path. -/
def leafCorner (P T w m : ℕ) : ℕ → ℤ × ℤ → List (ℕ × ℕ) → ℤ × ℤ
  | 0, c, _ => c
  | _ + 1, c, [] => c
  | r + 1, c, kl :: p => leafCorner P T w m r
      (c.1 + ((kl.1 * (w * P ^ (m + r)) : ℕ) : ℤ), c.2 + ((kl.2 * (w * T ^ (m + r)) : ℕ) : ℤ)) p

/-- **Restricted witness trees** (Lemma 12.1 proof, second paragraph; classical construction,
Lemma 4.6 proof, "Iteration of Lemma 4.2 produces a binary tree"). If the restriction of `F` to
a doubled box of rank `m + r` fails `(m+r)`-sparsity, some tree of the deterministic family has
every leaf failing `m`-sparsity on its region, the restriction to every ancestor being kept. -/
def RestrictedWitnessTrees : Prop :=
  ∀ (P T w : ℕ), 1 ≤ P → 1 ≤ T → 1 ≤ w → ∀ (m r : ℕ) (F : Set (ℤ × ℤ)) (a b : ℤ),
    ¬ Sparse P T w (m + r) (F ∩ box a b (2 * w * P ^ (m + r)) (2 * w * T ^ (m + r))) →
    ∃ t ∈ witnessTrees P T r, ∀ p ∈ t, ¬ Sparse P T w m (F ∩ treeRegion P T w m r a b p)

/-- Shape of the witness trees (Lemma 12.1 proof; classical construction, Lemma 4.6 proof): `2^r` leaves;
leaf regions pairwise disjoint; with the flush placement of Lemma 4.2 each leaf region is the
leaf's full doubled rank-`m` box (so the leaf boxes are disjoint too). -/
def WitnessTreeShape : Prop :=
  ∀ (P T w : ℕ), 1 ≤ P → 1 ≤ T → 1 ≤ w → ∀ (m r : ℕ) (a b : ℤ), ∀ t ∈ witnessTrees P T r,
    t.card = 2 ^ r ∧
    (∀ p ∈ t, ∀ p' ∈ t, p ≠ p' →
      Disjoint (treeRegion P T w m r a b p) (treeRegion P T w m r a b p')) ∧
    (∀ p ∈ t, treeRegion P T w m r a b p =
      box (leafCorner P T w m r (a, b) p).1 (leafCorner P T w m r (a, b) p).2
        (2 * w * P ^ m) (2 * w * T ^ m))

/-- Lemma 12.1 proof: "There are at most D_R^{N-1} geometric trees from a fixed root doubled
box"; classical construction, Lemma 4.6 proof: "at most C^{L-1} possible trees for fixed root". -/
def WitnessTreeCount : Prop :=
  ∀ P T r : ℕ, (witnessTrees P T r).card ≤ Dpair P T ^ (2 ^ r - 1)

/-- Mesh cover of a test rectangle (Lemma 12.1 proof, "a failing moving rank-k window meeting
its restricted flag set fits in one doubled rank-k box from the wP^k by wT^k mesh"; classical
construction, Lemma 4.2 proof, "A fixed multiple of V^{j+1} can be tested with a bounded cover
by full rank-j boxes"). -/
def MeshRootCover : Prop :=
  ∀ (P T w : ℕ), 1 ≤ P → 1 ≤ T → 1 ≤ w →
    ∀ (k : ℕ) (E : Set (ℤ × ℤ)) (a b : ℤ) (L M : ℕ),
      ¬ Sparse P T w k (E ∩ box a b L M) →
      ∃ il ∈ Finset.range (L / (w * P ^ k) + 1) ×ˢ Finset.range (M / (w * T ^ k) + 1),
        ¬ Sparse P T w k ((E ∩ box a b L M) ∩ childBox P T w k a b il)

/-- The area bound on the conflict degree (Lemma 12.1 proof, third paragraph): if stencils lie
within radii `(r_x, r_t)` of their site and the leaf regions are pairwise disjoint and lie in
`2w × 2w` boxes, each leaf's key set meets those of at most `J_R - 1` other leaves. -/
def ConflictDegreeArea : Prop :=
  ∀ {κ ι : Type} (sten : ℤ × ℤ → Finset κ) (pos : κ → ℤ × ℤ) (rx rt w : ℕ),
    (∀ q, ∀ k ∈ sten q, |(pos k).1 - q.1| ≤ rx ∧ |(pos k).2 - q.2| ≤ rt) →
    ∀ (region : ι → Set (ℤ × ℤ)) (corner : ι → ℤ × ℤ) (t : Finset ι),
      (∀ ℓ ∈ t, region ℓ ⊆ box (corner ℓ).1 (corner ℓ).2 (2 * w) (2 * w)) →
      (∀ ℓ ∈ t, ∀ ℓ' ∈ t, ℓ ≠ ℓ' → Disjoint (region ℓ) (region ℓ')) →
      ∀ ℓ ∈ t, ∃ C : Finset ι, C.card ≤ (2 * w + 4 * rx + 3) * (2 * w + 4 * rt + 3) - 1 ∧
        ∀ ℓ' ∈ t, ℓ' ≠ ℓ →
          ¬ Disjoint (⋃ q ∈ region ℓ, (sten q : Set κ)) (⋃ q ∈ region ℓ', (sten q : Set κ)) →
          ℓ' ∈ C

/-- **The general witness-tree probability bound** (the probabilistic core of Lemma 12.1):
independent keys of rate at most `e`, stencil flags with at most `s` keys, at most `NR` roots,
at most `D^{N-1}` trees per root, `N` leaves per tree with regions in `2w × 2w` boxes, key
conflict degree at most `J - 1`. If every outcome in `F` has some tree whose leaf regions all
contain a flag, then `μ F ≤ NR · D^{N-1} · (A e)^{N/J}` with `A = 4w²s`, when `A e ≤ 1`. -/
def WitnessTreeProbability : Prop :=
  ∀ {Ω κ ι ρ : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : κ → Ω → Bool), (∀ k, Measurable (X k)) → iIndepFun X μ →
    ∀ (e : ℝ), 0 ≤ e → (∀ k, μ {ω | X k ω = true} ≤ ENNReal.ofReal e) →
    ∀ (sten : ℤ × ℤ → Finset κ) (s w : ℕ), (∀ q, (sten q).card ≤ s) →
    ∀ (region : ι → Set (ℤ × ℤ)) (corner : ι → ℤ × ℤ)
      (roots : Finset ρ) (trees : ρ → Finset (Finset ι)) (NR D N J : ℕ),
      roots.card ≤ NR → (∀ x ∈ roots, (trees x).card ≤ D ^ (N - 1)) →
      (∀ x ∈ roots, ∀ t ∈ trees x, t.card = N) →
      (∀ x ∈ roots, ∀ t ∈ trees x, ∀ ℓ ∈ t,
        region ℓ ⊆ box (corner ℓ).1 (corner ℓ).2 (2 * w) (2 * w)) →
      1 ≤ J →
      (∀ x ∈ roots, ∀ t ∈ trees x, ∀ ℓ ∈ t, ∃ C : Finset ι, C.card ≤ J - 1 ∧
        ∀ ℓ' ∈ t, ℓ' ≠ ℓ →
          ¬ Disjoint (⋃ q ∈ region ℓ, (sten q : Set κ)) (⋃ q ∈ region ℓ', (sten q : Set κ)) →
          ℓ' ∈ C) →
      ∀ F : Set Ω, (∀ ω ∈ F, ∃ x ∈ roots, ∃ t ∈ trees x, ∀ ℓ ∈ t,
          (stencilFlags sten (fun k => X k ω) ∩ region ℓ).Nonempty) →
        (4 * w ^ 2 * s : ℝ) * e ≤ 1 →
        μ F ≤ ENNReal.ofReal ((NR : ℝ) * (D : ℝ) ^ (N - 1) *
          ((4 * w ^ 2 * s : ℝ) * e) ^ ((N : ℝ) / (J : ℝ)))

/-! The explicit constants of Lemma 12.1. -/
namespace Q1

/-- `D_R = 8(P_R+2)^2(T_R+2)^2`. -/
def DR (P T : ℕ) : ℕ := Dpair P T
/-- `N_R = 4(P_R+3)(T_R+3)`. -/
def NR (P T : ℕ) : ℕ := 4 * (P + 3) * (T + 3)
/-- `A_R = 4 w_R^2 s_R`. -/
def AR (w s : ℕ) : ℕ := 4 * w ^ 2 * s
/-- `J_R = (2w_R+4r_x+3)(2w_R+4r_t+3)`. -/
def JR (w rx rt : ℕ) : ℕ := (2 * w + 4 * rx + 3) * (2 * w + 4 * rt + 3)
/-- `Δ_R = J_R - 1`. -/
def ΔR (w rx rt : ℕ) : ℕ := JR w rx rt - 1
/-- `c_R = 1/J_R`. -/
noncomputable def cR (w rx rt : ℕ) : ℝ := 1 / (JR w rx rt : ℝ)
/-- `C_R = N_R D_R A_R^{1/J_R}`. -/
noncomputable def CR (P T w s rx rt : ℕ) : ℝ :=
  (NR P T : ℝ) * (DR P T : ℝ) * (AR w s : ℝ) ^ (1 / (JR w rx rt : ℝ))
/-- `e_R0 = A_R^{-1}(2N_R D_R)^{-J_R}`. -/
noncomputable def eR0 (P T w s rx rt : ℕ) : ℝ :=
  (AR w s : ℝ)⁻¹ * ((2 * NR P T * DR P T : ℕ) : ℝ) ^ (-(JR w rx rt : ℤ))
/-- `z_{R,j}(e) = [C_R e^{c_R}]^{2^{j-1}}`. -/
noncomputable def zR (P T w s rx rt j : ℕ) (e : ℝ) : ℝ :=
  (CR P T w s rx rt * e ^ cR w rx rt) ^ (2 ^ (j - 1))

end Q1

/-- **Lemma 12.1** (quantum storage paper, version 3.0, "restricted witness trees and their
probability"), first assertion: "For any prescribed protected rank-j W_0 test of width
< w_R P_R^j and height < w_R T_R^j, its failure of (j-1)-sparsity has probability at most
z_{R,j}(e) = [C_R e^{c_R}]^{2^{j-1}}, j ≥ 1." Flags: OR of independent keys in a stencil of
at most `s` keys within radii `(r_x, r_t)`; key rates at most `e` (unequal allowed). -/
def Q1_L1 : Prop :=
  ∀ (P T w s rx rt : ℕ), 1 ≤ P → 1 ≤ T → 1 ≤ w → 1 ≤ s →
  ∀ {κ : Type} (sten : ℤ × ℤ → Finset κ) (pos : κ → ℤ × ℤ),
    (∀ q, (sten q).card ≤ s) →
    (∀ q, ∀ k ∈ sten q, |(pos k).1 - q.1| ≤ rx ∧ |(pos k).2 - q.2| ≤ rt) →
  ∀ (p : κ → NNReal) (hp : ∀ k, p k ≤ 1) (e : ℝ), 0 ≤ e → (∀ k, (p k : ℝ) ≤ e) →
  ∀ (j : ℕ), 1 ≤ j → ∀ (a b : ℤ) (L M : ℕ), L < w * P ^ j → M < w * T ^ j →
    keyNoise p hp {ω | ¬ Sparse P T w (j - 1) (stencilFlags sten ω ∩ box a b L M)} ≤
      ENNReal.ofReal (Q1.zR P T w s rx rt j e)

/-- **Lemma 12.1**, second assertion: "In particular C_R e^{c_R} ≤ 1/2 for
0 ≤ e ≤ e_R0", with "The asserted threshold ... also ensures A_R e ≤ 1". -/
def Q1_L1_Threshold : Prop :=
  ∀ (P T w s rx rt : ℕ), 1 ≤ w → 1 ≤ s → ∀ e : ℝ, 0 ≤ e → e ≤ Q1.eR0 P T w s rx rt →
    Q1.CR P T w s rx rt * e ^ Q1.cR w rx rt ≤ 1 / 2 ∧ (Q1.AR w s : ℝ) * e ≤ 1

/-- **Lemma 4.2 of the classical construction, probabilistic part** (p. 10), independent
replacement flags of rates at most `u` (the stencil of `q` is `q` itself).
(i) every full doubled rank-`j` box: "b_j ≤ D^{-1}(4Dw^2u)^{2^j}";
(ii) "≤ D^{-1}u^{2^{j-1}} if u ≤ (4Dw^2)^{-2}";
(iii) "the probability of j-nonsparsity on a prescribed fixed multiple of V^{j+1} is at most
C_0 u^{c_0 2^j}", here with the explicit `C_0 = (m_x P + 1)(m_t T + 1)/D`, `c_0 = 1/2`, for
every multiple `m_x P^{j+1} × m_t T^{j+1}` and every translate. -/
def Lemma_4_2_Probability : Prop :=
  ∀ (P T w : ℕ), 1 ≤ P → 1 ≤ T → 1 ≤ w →
  ∀ (p : ℤ × ℤ → NNReal) (hp : ∀ z, p z ≤ 1) (u : ℝ), 0 ≤ u → (∀ z, (p z : ℝ) ≤ u) →
    (∀ (j : ℕ) (a b : ℤ),
      keyNoise p hp
          {ω | ¬ Sparse P T w j ({z | ω z = true} ∩ box a b (2 * w * P ^ j) (2 * w * T ^ j))} ≤
        ENNReal.ofReal ((Dpair P T : ℝ)⁻¹ * (4 * (Dpair P T : ℝ) * w ^ 2 * u) ^ (2 ^ j))) ∧
    (u ≤ ((4 * (Dpair P T : ℝ) * w ^ 2) ^ 2)⁻¹ →
      (∀ (j : ℕ) (a b : ℤ),
        keyNoise p hp
            {ω | ¬ Sparse P T w j ({z | ω z = true} ∩ box a b (2 * w * P ^ j) (2 * w * T ^ j))} ≤
          ENNReal.ofReal ((Dpair P T : ℝ)⁻¹ * u ^ ((2 : ℝ) ^ ((j : ℝ) - 1)))) ∧
      (∀ (mx my j : ℕ) (a b : ℤ),
        keyNoise p hp
            {ω | ¬ Sparse P T w j
              ({z | ω z = true} ∩ box a b (mx * P ^ (j + 1)) (my * T ^ (j + 1)))} ≤
          ENNReal.ofReal ((((mx * P + 1) * (my * T + 1) : ℕ) : ℝ) / (Dpair P T : ℝ) *
            u ^ ((1 / 2 : ℝ) * 2 ^ j))))

/-- Classical construction, Lemma 4.6 proof, p. 15 (Δ_leaf): "after scaling the two axes each neighboring
original leaf is a disjoint unit rectangle lying within a bounded box". Pairwise disjoint
doubled boxes of sides `2S × 2S'`, each enlarged by `a_x S` and `a_y S'` on every side: the
enlargements meeting a given one belong to at most `(3+2a_x)(3+2a_y) - 1` other boxes. -/
def LeafOverlapDegree : Prop :=
  ∀ {ι : Type} (S S' ax ay : ℕ) (corner : ι → ℤ × ℤ) (fam : Finset ι), 1 ≤ S → 1 ≤ S' →
    (∀ ℓ ∈ fam, ∀ ℓ' ∈ fam, ℓ ≠ ℓ' →
      Disjoint (box (corner ℓ).1 (corner ℓ).2 (2 * S) (2 * S'))
        (box (corner ℓ').1 (corner ℓ').2 (2 * S) (2 * S'))) →
    ∀ ℓ ∈ fam, ∃ C : Finset ι, C.card ≤ (3 + 2 * ax) * (3 + 2 * ay) - 1 ∧
      ∀ ℓ' ∈ fam, ℓ' ≠ ℓ →
        ¬ Disjoint
          (box ((corner ℓ).1 - ((ax * S : ℕ) : ℤ)) ((corner ℓ).2 - ((ay * S' : ℕ) : ℤ))
            ((2 + 2 * ax) * S) ((2 + 2 * ay) * S'))
          (box ((corner ℓ').1 - ((ax * S : ℕ) : ℤ)) ((corner ℓ').2 - ((ay * S' : ℕ) : ℤ))
            ((2 + 2 * ax) * S) ((2 + 2 * ay) * S')) →
        ℓ' ∈ C

/-- Classical construction, Lemma 4.6 proof, p. 15 (exponent bookkeeping): "Choose D_s>12d_s+10 and
M_s>max(8d_s,(Δ_leaf+1)(D_s+1)+2d_s) ... For small p, (4) bounds raw-plus-short nonsparsity
at i>j_s by p^{D_s 2^{i-j_s}}." Core step: if the leaf probability is at most `K p^{M-2d}`
with `M > (Δ+1)(D+1) + 2d`, then `(C α^{1/(Δ+1)})^{2^n} ≤ p^{D 2^n}` for every
`0 < p ≤ 1` with `C K^{1/(Δ+1)} p ≤ 1` (an explicit smallness condition). -/
def ExponentBookkeeping : Prop :=
  ∀ (C K M d : ℝ) (Δ D : ℕ), 0 ≤ C → 0 ≤ K → ((Δ : ℝ) + 1) * ((D : ℝ) + 1) + 2 * d < M →
    ∀ p : ℝ, 0 < p → p ≤ 1 → C * K ^ (1 / ((Δ : ℝ) + 1)) * p ≤ 1 →
      ∀ α : ℝ, 0 ≤ α → α ≤ K * p ^ (M - 2 * d) →
        ∀ n : ℕ, (C * α ^ (1 / ((Δ : ℝ) + 1))) ^ (2 ^ n) ≤ p ^ (D * 2 ^ n)

/-- Classical construction, Lemma 4.6, first conclusion, for raw flags (p. 15: "The same two conclusions hold
for raw flags alone at all sufficiently small fixed rates"): the sum over all ranks `j ≥ 1`
of the failure probabilities of one prescribed `(j-1)`-sparsity test in a fixed multiple of
`V^j` is less than `1/4`, uniformly in the translations, for every rate below an explicit
cutoff. -/
def NestedTestSumRaw : Prop :=
  ∀ (P T w mx my : ℕ), 1 ≤ P → 1 ≤ T → 1 ≤ w →
  ∀ (p : ℤ × ℤ → NNReal) (hp : ∀ z, p z ≤ 1) (u : ℝ), 0 ≤ u → (∀ z, (p z : ℝ) ≤ u) →
    u ≤ ((4 * (Dpair P T : ℝ) * w ^ 2) ^ 2)⁻¹ →
    u < (64 * ((((mx * P + 1) * (my * T + 1) : ℕ) : ℝ) / (Dpair P T : ℝ)) ^ 2)⁻¹ →
    ∀ (a b : ℕ → ℤ),
      ∑' j : ℕ, keyNoise p hp
          {ω | ¬ Sparse P T w j
            ({z | ω z = true} ∩ box (a j) (b j) (mx * P ^ (j + 1)) (my * T ^ (j + 1)))} <
        ENNReal.ofReal (1 / 4)

end Flagship1D
