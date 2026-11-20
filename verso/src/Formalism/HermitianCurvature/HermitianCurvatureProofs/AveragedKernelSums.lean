import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses

set_option maxHeartbeats 400000

noncomputable section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace AveragedKernelSums

open Formalism.FourierDecayAlt.P.A5x6

/- English proof (translation)
Introduce `a`. Establish `E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c : ℂ) * k x y) = (c : ℂ) * ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[E]`. Take `⟨h1, h2⟩` from `h a`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Complex.im_ofReal_mul, h1, mul_zero]`. Rewrite using `[Complex.re_ofReal_mul]`. Conclude with `mul_nonneg hc h2`.
-/
theorem psd_smul {X : Type} (F : Finset X) (k : X → X → ℂ) (c : ℝ) (hc : 0 ≤ c) (h : IsPSD F k) :
    IsPSD F (fun x y => (c : ℂ) * k x y) := by
  intro a
  have E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c : ℂ) * k x y) =
      (c : ℂ) * ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [E]
  obtain ⟨h1, h2⟩ := h a
  constructor
  · rw [Complex.im_ofReal_mul, h1, mul_zero]
  · rw [Complex.re_ofReal_mul]; exact mul_nonneg hc h2

/- English proof (translation)
Introduce `a`. Establish `E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (∑ i ∈ s, k i x y) = ∑ i ∈ s, ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k i x y`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Rewrite using `[E, Complex.im_sum, Complex.re_sum]`. Conclude with `⟨Finset.sum_eq_zero fun i hi => (h i hi a).1, Finset.sum_nonneg fun i hi => (h i hi a).2⟩`.
-/
theorem psd_sum {X ι : Type} (F : Finset X) (s : Finset ι) (k : ι → X → X → ℂ)
    (h : ∀ i ∈ s, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  intro a
  have E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (∑ i ∈ s, k i x y) =
      ∑ i ∈ s, ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k i x y := by
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  rw [E, Complex.im_sum, Complex.re_sum]
  exact ⟨Finset.sum_eq_zero fun i hi => (h i hi a).1, Finset.sum_nonneg fun i hi => (h i hi a).2⟩

/- English proof (translation)
Introduce `a`. Establish `E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (∑ b ∈ B, ∑ b' ∈ B, e b * conj (e b') * k (x, b) (y, b')) = ∑ q ∈ F ×ˢ B, ∑ q' ∈ F ×ˢ B, (a q.1 * e q.2) * conj (a q'.1 * e q'.2) * k q q'`. Rewrite using `[Finset.sum_product]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_product]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[E]`. Conclude with `h _`.
-/
theorem psd_mix {X Y : Type} (F : Finset X) (B : Finset Y) (e : Y → ℂ)
    (k : X × Y → X × Y → ℂ) (h : IsPSD (F ×ˢ B) k) :
    IsPSD F (fun x x' => ∑ b ∈ B, ∑ b' ∈ B, e b * conj (e b') * k (x, b) (x', b')) := by
  intro a
  have E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) *
        (∑ b ∈ B, ∑ b' ∈ B, e b * conj (e b') * k (x, b) (y, b')) =
      ∑ q ∈ F ×ˢ B, ∑ q' ∈ F ×ˢ B, (a q.1 * e q.2) * conj (a q'.1 * e q'.2) * k q q' := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_product]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [map_mul]; ring
  rw [E]
  exact h _

section Basic

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

/- English proof (translation)
Use `(hL.selfDual 1).2 R.one_mem r hr` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem psi_R (hL : LocalDatum K R ψ) {r : K} (hr : r ∈ R) : ψ r = 1 := by
  have := (hL.selfDual 1).2 R.one_mem r hr
  rwa [one_mul] at this

/- English proof (translation)
Establish `h1 : ∀ b ∈ B, ψ (-((z + r) * b)) = ψ (-(z * b))`. Introduce `b hb`. Establish `: ψ (-(r * b)) = 1` using `psi_R hD (R.neg_mem (R.mul_mem hr (hB b hb)))`. Establish `e : -((z + r) * b) = -(z * b) + (-(r * b))` using `by ring`. Rewrite using `[e, AddChar.map_add_eq_mul, this, mul_one]`.

Use function extensionality and compare the values at `h h'`. Unfold `thx`. Use `congr 1`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_` and prove the remaining obligations. Rewrite using `[h1 b hb, h1 b' hb']`.
-/
theorem thx_periodic (hD : LocalDatum K R ψ) (m : ℕ) (A B : Finset K) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hB : ∀ b ∈ B, b ∈ R) (z r : K) (hr : r ∈ R) :
    thx R ψ m cr A B τ (z + r) = thx R ψ m cr A B τ z := by
  have h1 : ∀ b ∈ B, ψ (-((z + r) * b)) = ψ (-(z * b)) := by
    intro b hb
    have : ψ (-(r * b)) = 1 := psi_R hD (R.neg_mem (R.mul_mem hr (hB b hb)))
    have e : -((z + r) * b) = -(z * b) + (-(r * b)) := by ring
    rw [e, AddChar.map_add_eq_mul, this, mul_one]
  funext h h'
  unfold thx
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
  rw [h1 b hb, h1 b' hb']

/- English proof (translation)
Establish `h1 : ∀ ρ : K, IsPSD F (fun h h' => ∑ b ∈ B, ∑ b' ∈ B, ψ (-(z * b)) * conj (ψ (-(z * b'))) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')))`. Introduce `ρ`. Use `psd_mix F B (fun b => ψ (-(z * b))) (fun q q' => uGram R ψ m cr Set.univ q.1 q'.1 (τ (ρ + q.2)) (τ (ρ + q'.2))) ?_` and prove the remaining obligations. Use `psd_comap (fun p p' : Point K × Kˣ => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2) (fun q : Point K × K => (q.1, τ (ρ + q.2))) (F ×ˢ B) (hG _ ?_ m cr hcr)` and prove the remaining obligations. Introduce `p hp p' hp'`.

Take `⟨q, hq, rfl⟩` from `Finset.mem_image.mp hp`. Take `⟨q', hq', rfl⟩` from `Finset.mem_image.mp hp'`. Conclude with `(hF _ (Finset.mem_product.mp hq).1).trans (hF _ (Finset.mem_product.mp hq').1).symm`. Establish `h2` using `psd_smul F _ ((A.card : ℝ)⁻¹) (by positivity) (psd_sum F A _ fun ρ _ => psd_smul F _ (((B.card : ℝ)⁻¹) ^ 2) (by positivity) (h1 ρ))`. Establish `e : thx R ψ m cr A B τ z = fun h h' => (((A.card : ℝ)⁻¹ : ℝ) : ℂ) * ∑ ρ ∈ A, ((((B.card : ℝ)⁻¹) ^ 2 : ℝ) : ℂ) * ∑ b ∈ B, ∑ b' ∈ B, ψ (-(z * b)) * conj (ψ (-(z * b'))) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b'))`.

Use function extensionality and compare the values at `h h'`. Unfold `thx`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `h2`.
-/
theorem thx_psd (hG : ∀ F' : Finset (Point K × Kˣ), (∀ p ∈ F', ∀ p' ∈ F', p.1.1.sum = p'.1.1.sum) →
      ∀ (m : ℕ) (cr : K ⧸ R.toAddSubgroup → Kˣ), IsCr R cr →
      IsPSD F' (fun p p' => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2))
    (m n₀ : ℕ) (F : Finset (Point K)) (A B : Finset K) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hF : ∀ h ∈ F, h.1.sum = n₀) (hcr : IsCr R cr) (z : K) :
    IsPSD F (thx R ψ m cr A B τ z) := by
  classical
  have h1 : ∀ ρ : K, IsPSD F (fun h h' => ∑ b ∈ B, ∑ b' ∈ B,
      ψ (-(z * b)) * conj (ψ (-(z * b'))) *
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b'))) := by
    intro ρ
    refine psd_mix F B (fun b => ψ (-(z * b)))
      (fun q q' => uGram R ψ m cr Set.univ q.1 q'.1 (τ (ρ + q.2)) (τ (ρ + q'.2))) ?_
    refine psd_comap (fun p p' : Point K × Kˣ => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2)
      (fun q : Point K × K => (q.1, τ (ρ + q.2))) (F ×ˢ B) (hG _ ?_ m cr hcr)
    intro p hp p' hp'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
    exact (hF _ (Finset.mem_product.mp hq).1).trans (hF _ (Finset.mem_product.mp hq').1).symm
  have h2 := psd_smul F _ ((A.card : ℝ)⁻¹) (by positivity)
    (psd_sum F A _ fun ρ _ => psd_smul F _ (((B.card : ℝ)⁻¹) ^ 2) (by positivity) (h1 ρ))
  have e : thx R ψ m cr A B τ z = fun h h' => (((A.card : ℝ)⁻¹ : ℝ) : ℂ) * ∑ ρ ∈ A,
      ((((B.card : ℝ)⁻¹) ^ 2 : ℝ) : ℂ) * ∑ b ∈ B, ∑ b' ∈ B,
        ψ (-(z * b)) * conj (ψ (-(z * b'))) *
          uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) := by
    funext h h'
    unfold thx
    push_cast
    rfl
  rw [e]
  exact h2

end Basic

/- English proof (translation)
Take `⟨ϖ, hϖ, hϖx⟩` from `hL.unif`. Establish `hN : ∃ N : ℕ, (∀ h ∈ F, (ϖ : K) ^ N * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) ∈ R) ∧ ((∀ h ∈ F, InGLR R h) → N = 0)`. Distinguish the cases in `hG : ∀ h ∈ F, InGLR R h`. Use `⟨0, fun h hh => ?_, fun _ => rfl⟩` and prove the remaining obligations. Take `⟨_, h2, h3⟩` from `glr_det R h (hG h hh)`.

Establish `e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1` using `IsUnit.val_inv_mul (pt_det_isUnit h)`. Establish `e : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) = (pt h.1 h.2)⁻¹.det`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_zero, one_mul, e]`. Conclude with `h2`.

Use `choose M hM using fun h : Point K => hϖx (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)`. Use `⟨F.sup M, fun h hh => ?_, fun h => absurd h hG⟩` and prove the remaining obligations. Establish `hle : M h ≤ F.sup M` using `Finset.le_sup (f := M) hh`. Establish `e3 : (ϖ : K) ^ (F.sup M) = (ϖ : K) ^ (F.sup M - M h) * (ϖ : K) ^ M h`. Rewrite using `[← pow_add, Nat.sub_add_cancel hle]`.

Rewrite using `[e3, mul_assoc]`. Conclude with `R.mul_mem (R.pow_mem hϖ _) (hM h)`. Take `⟨N, hN1, hN2⟩` from `hN`. Set `L : Submodule R K` to `{ carrier := {x | (ϖ : K) ^ N * x ∈ R} add_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_ofPred_eq] at ha hb ⊢`. Rewrite using `[mul_add]`. Conclude with `R.add_mem ha hb`. Use the proof step `zero_mem' := by simp [R.zero_mem]`. Use the proof step `smul_mem' := by`.

Introduce `c x hx`. Simplify using `only [Set.mem_ofPred_eq] at hx ⊢`. Rewrite using `[Subring.smul_def, smul_eq_mul, mul_left_comm]`. Conclude with `R.mul_mem c.2 hx }`. Use `⟨L, ⟨?_, ?_, fun r hr => R.mul_mem (R.pow_mem hϖ N) hr, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `hL.isOpen.preimage (continuous_const_mul ((ϖ : K) ^ N))`. Establish `: (L : Set K) = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) '' (R : Set K)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Use `⟨(ϖ : K) ^ N * x, hx, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]`. Introduce and unpack `⟨y, hy, rfl⟩ show (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * y) ∈ R`. Rewrite using `[← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]`.

Conclude with `hy`. Rewrite using `[this]`. Conclude with `hL.isCompact.image (continuous_const_mul _)`. Introduce `t ht h hh h' _`. Assume the negation of the conclusion as `h0`.

Apply `ht` to reduce the goal to its premises. Establish `h4` using `(hSup K R ψ s hs h h' t t h0).1`. Use `show (ϖ : K) ^ N * (t : K) ∈ R`. Establish `e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1` using `IsUnit.val_inv_mul (pt_det_isUnit h)`. Establish `e : (ϖ : K) ^ N * (t : K) = ((ϖ : K) ^ N * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)) * ((pt h.1 h.2).det * (t : K))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `R.mul_mem (hN1 h hh) h4`. Introduce `hG x show (ϖ : K) ^ N * x ∈ R ↔ x ∈ R`. Rewrite using `[hN2 hG, pow_zero, one_mul]`.
-/
theorem supportModule_of (hSup : NsSupport) (K : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (R : Subring K) (ψ : AddChar K ℂ) (hL : LocalDatum K R ψ) (s : ℕ)
    (F : Finset (Point K)) (hs : 1 ≤ s) :
    ∃ Lc : Submodule R K, IsCutModule R ψ s F Lc ∧
      ((∀ h ∈ F, InGLR R h) → ∀ x, x ∈ Lc ↔ x ∈ R) := by
  classical
  obtain ⟨ϖ, hϖ, hϖx⟩ := hL.unif
  have hN : ∃ N : ℕ, (∀ h ∈ F, (ϖ : K) ^ N * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) ∈ R) ∧
      ((∀ h ∈ F, InGLR R h) → N = 0) := by
    by_cases hG : ∀ h ∈ F, InGLR R h
    · refine ⟨0, fun h hh => ?_, fun _ => rfl⟩
      obtain ⟨_, h2, h3⟩ := glr_det R h (hG h hh)
      have e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1 :=
        IsUnit.val_inv_mul (pt_det_isUnit h)
      have e : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) = (pt h.1 h.2)⁻¹.det := by
        calc (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)
            = (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) *
                ((pt h.1 h.2).det * (pt h.1 h.2)⁻¹.det) := by rw [h3, mul_one]
          _ = (pt h.1 h.2)⁻¹.det := by rw [← mul_assoc, e2, one_mul]
      rw [pow_zero, one_mul, e]; exact h2
    · choose M hM using fun h : Point K => hϖx (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)
      refine ⟨F.sup M, fun h hh => ?_, fun h => absurd h hG⟩
      have hle : M h ≤ F.sup M := Finset.le_sup (f := M) hh
      have e3 : (ϖ : K) ^ (F.sup M) = (ϖ : K) ^ (F.sup M - M h) * (ϖ : K) ^ M h := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [e3, mul_assoc]; exact R.mul_mem (R.pow_mem hϖ _) (hM h)
  obtain ⟨N, hN1, hN2⟩ := hN
  let L : Submodule R K :=
    { carrier := {x | (ϖ : K) ^ N * x ∈ R}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [mul_add]; exact R.add_mem ha hb
      zero_mem' := by simp [R.zero_mem]
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [Subring.smul_def, smul_eq_mul, mul_left_comm]
        exact R.mul_mem c.2 hx }
  refine ⟨L, ⟨?_, ?_, fun r hr => R.mul_mem (R.pow_mem hϖ N) hr, ?_⟩, ?_⟩
  · exact hL.isOpen.preimage (continuous_const_mul ((ϖ : K) ^ N))
  · have : (L : Set K) = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) '' (R : Set K) := by
      ext x
      constructor
      · intro hx
        refine ⟨(ϖ : K) ^ N * x, hx, ?_⟩
        simp only
        rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
      · rintro ⟨y, hy, rfl⟩
        show (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * y) ∈ R
        rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
        exact hy
    rw [this]
    exact hL.isCompact.image (continuous_const_mul _)
  · intro t ht h hh h' _
    by_contra h0
    apply ht
    have h4 := (hSup K R ψ s hs h h' t t h0).1
    show (ϖ : K) ^ N * (t : K) ∈ R
    have e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1 :=
      IsUnit.val_inv_mul (pt_det_isUnit h)
    have e : (ϖ : K) ^ N * (t : K) = ((ϖ : K) ^ N * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)) *
        ((pt h.1 h.2).det * (t : K)) := by
      calc (ϖ : K) ^ N * (t : K) = (ϖ : K) ^ N * ((((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) *
            (pt h.1 h.2).det) * (t : K) := by rw [e2, mul_one]
        _ = _ := by ring
    rw [e]
    exact R.mul_mem (hN1 h hh) h4
  · intro hG x
    show (ϖ : K) ^ N * x ∈ R ↔ x ∈ R
    rw [hN2 hG, pow_zero, one_mul]

section Sum

variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}

/- English proof (translation)
Establish `h1 : ((Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) : K) : K ⧸ R.toAddSubgroup) = (z : K ⧸ R.toAddSubgroup)` using `QuotientAddGroup.out_eq' _`. Establish `h3` using `R.toAddSubgroup.neg_mem (QuotientAddGroup.eq.mp h1)`. Establish `e : -(-(Quotient.out ((z : K) : K ⧸ R.toAddSubgroup)) + z) = Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z` using `by ring`. Rewrite `h3` using `[e]`. Conclude with `h3`.
-/
theorem out_sub_mem (z : K) : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z ∈ R := by
  have h1 : ((Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) : K) : K ⧸ R.toAddSubgroup) =
      (z : K ⧸ R.toAddSubgroup) := QuotientAddGroup.out_eq' _
  have h3 := R.toAddSubgroup.neg_mem (QuotientAddGroup.eq.mp h1)
  have e : -(-(Quotient.out ((z : K) : K ⧸ R.toAddSubgroup)) + z) =
      Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z := by ring
  rw [e] at h3; exact h3

/- English proof (translation)
Establish `e : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) * c = z * c + (Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z) * c` using `by ring`. Rewrite using `[e, AddChar.map_add_eq_mul, hψ _ (R.mul_mem (out_sub_mem z) hc), mul_one]`.
-/
theorem psi_out (hψ : ∀ r ∈ R, ψ r = 1) {c : K} (hc : c ∈ R) (z : K) :
    ψ (Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) * c) = ψ (z * c) := by
  have e : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) * c =
      z * c + (Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z) * c := by ring
  rw [e, AddChar.map_add_eq_mul, hψ _ (R.mul_mem (out_sub_mem z) hc), mul_one]

/- English proof (translation)
Establish `h : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z ∈ P` using `hRP (out_sub_mem z)`. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Use `P.sub_mem h1 h` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Introduce `h1`. Use `P.add_mem h h1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem mem_out {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P) (z : K) :
    Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) ∈ P ↔ z ∈ P := by
  have h : Quotient.out ((z : K) : K ⧸ R.toAddSubgroup) - z ∈ P := hRP (out_sub_mem z)
  constructor
  · intro h1
    have := P.sub_mem h1 h
    rwa [sub_sub_cancel] at this
  · intro h1
    have := P.add_mem h h1
    rwa [sub_add_cancel] at this

/- English proof (translation)
Establish `h` using `AddSubgroup.relIndex_comap (⊥ : AddSubgroup (K ⧸ M)) (QuotientAddGroup.mk' M) L`. Rewrite `h` using `[AddSubgroup.relIndex_bot_left]`. Rewrite using `[← h]`. Use `congr 1`. Use extensionality with `x`.

Simplify using the standard rewrite rules.
-/
theorem relIndex_eq_card_map (M L : AddSubgroup K) :
    M.relIndex L = Nat.card (L.map (QuotientAddGroup.mk' M)) := by
  have h := AddSubgroup.relIndex_comap (⊥ : AddSubgroup (K ⧸ M)) (QuotientAddGroup.mk' M) L
  rw [AddSubgroup.relIndex_bot_left] at h
  rw [← h]
  congr 1
  ext x
  simp

/- English proof (translation)
Rewrite using `[relIndex_eq_card_map]`. Establish `: {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ P} = ((P.map (QuotientAddGroup.mk' R.toAddSubgroup) : AddSubgroup _) : Set _)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨Quotient.out x, hx, QuotientAddGroup.out_eq' x⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `(mem_out hRP z).2 hz`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem card_alt {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P) :
    Nat.card {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ P} = R.toAddSubgroup.relIndex P := by
  rw [relIndex_eq_card_map]
  have : {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ P} =
      ((P.map (QuotientAddGroup.mk' R.toAddSubgroup) : AddSubgroup _) : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨Quotient.out x, hx, QuotientAddGroup.out_eq' x⟩
    · rintro ⟨z, hz, rfl⟩
      exact (mem_out hRP z).2 hz
  rw [this]
  rfl

/- English proof (translation)
Rewrite using `[relIndex_eq_card_map]`. Set `f : S → L.map (QuotientAddGroup.mk' M)` to `fun a => ⟨(a : K), ⟨a, h.1 a a.2, rfl⟩⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `a a' haa`.

Establish `h1 : ((a : K) : K ⧸ M) = ((a' : K) : K ⧸ M)` using `congrArg Subtype.val haa`. Establish `h2` using `QuotientAddGroup.eq.mp h1`. Take `⟨b, _, hb⟩` from `h.2 a' (h.1 a' a'.2)`. Establish `e1 : (a : K) = b` using `hb a ⟨a.2, by rwa [sub_eq_neg_add]⟩`. Establish `e2 : (a' : K) = b` using `hb a' ⟨a'.2, by rw [sub_self]; exact M.zero_mem⟩`.

Conclude with `Subtype.ext (e1.trans e2.symm)`. Introduce and unpack `⟨_, l, hl, rfl⟩`. Take `⟨b, ⟨hb1, hb2⟩, _⟩` from `h.2 l hl`. Use `⟨⟨b, hb1⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show ((b : K) : K ⧸ M) = ((l : K) : K ⧸ M)`.

Rewrite using `[QuotientAddGroup.eq, ← sub_eq_neg_add]`. Conclude with `hb2`. Rewrite using `[← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]`.
-/
theorem reps_card (L M : AddSubgroup K) (S : Finset K) (h : IsReps S L M) :
    M.relIndex L = S.card := by
  rw [relIndex_eq_card_map]
  let f : S → L.map (QuotientAddGroup.mk' M) := fun a => ⟨(a : K), ⟨a, h.1 a a.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 : ((a : K) : K ⧸ M) = ((a' : K) : K ⧸ M) := congrArg Subtype.val haa
      have h2 := QuotientAddGroup.eq.mp h1
      obtain ⟨b, _, hb⟩ := h.2 a' (h.1 a' a'.2)
      have e1 : (a : K) = b := hb a ⟨a.2, by rwa [sub_eq_neg_add]⟩
      have e2 : (a' : K) = b := hb a' ⟨a'.2, by rw [sub_self]; exact M.zero_mem⟩
      exact Subtype.ext (e1.trans e2.symm)
    · rintro ⟨_, l, hl, rfl⟩
      obtain ⟨b, ⟨hb1, hb2⟩, _⟩ := h.2 l hl
      refine ⟨⟨b, hb1⟩, Subtype.ext ?_⟩
      show ((b : K) : K ⧸ M) = ((l : K) : K ⧸ M)
      rw [QuotientAddGroup.eq, ← sub_eq_neg_add]
      exact hb2
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]

/- English proof (translation)
Establish `hx : ∀ x : K ⧸ R.toAddSubgroup, x + ((z₀ : K) : K ⧸ R.toAddSubgroup) = ((Quotient.out x + z₀ : K) : K ⧸ R.toAddSubgroup)`. Introduce `x`. Rewrite using `[QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']`. Establish `hs : ∑ x ∈ Tf, ψ (Quotient.out (x + ((z₀ : K) : K ⧸ R.toAddSubgroup)) * c) = ∑ x ∈ Tf, ψ (Quotient.out x * c)`. Use `Finset.sum_equiv (Equiv.addRight ((z₀ : K) : K ⧸ R.toAddSubgroup)) ?_ ?_` and prove the remaining obligations.

Introduce `x show x ∈ Tf ↔ x + ((z₀ : K) : K ⧸ R.toAddSubgroup) ∈ Tf`. Rewrite using `[hTf, hTf, hx, mem_out hRP, P.add_mem_cancel_right hz]`. Introduce `x _`. Both sides reduce to the same expression. Establish `hv : ∀ x : K ⧸ R.toAddSubgroup, ψ (Quotient.out (x + ((z₀ : K) : K ⧸ R.toAddSubgroup)) * c) = ψ (Quotient.out x * c) * ψ (z₀ * c)`.

Introduce `x`. Rewrite using `[hx, psi_out hψ hc, add_mul, AddChar.map_add_eq_mul]`. Simplify using `only [hv] at hs`. Rewrite `hs` using `[← Finset.sum_mul]`. Establish `h0 : (∑ x ∈ Tf, ψ (Quotient.out x * c)) * (ψ (z₀ * c) - 1) = 0`.

Rewrite using `[mul_sub, hs, mul_one, sub_self]`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (sub_eq_zero.mp h) hne`.
-/
theorem orth (hψ : ∀ r ∈ R, ψ r = 1) {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P)
    (Tf : Finset (K ⧸ R.toAddSubgroup)) (hTf : ∀ x, x ∈ Tf ↔ Quotient.out x ∈ P) {c z₀ : K}
    (hc : c ∈ R) (hz : z₀ ∈ P) (hne : ψ (z₀ * c) ≠ 1) :
    ∑ x ∈ Tf, ψ (Quotient.out x * c) = 0 := by
  have hx : ∀ x : K ⧸ R.toAddSubgroup, x + ((z₀ : K) : K ⧸ R.toAddSubgroup) =
      ((Quotient.out x + z₀ : K) : K ⧸ R.toAddSubgroup) := by
    intro x
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  have hs : ∑ x ∈ Tf, ψ (Quotient.out (x + ((z₀ : K) : K ⧸ R.toAddSubgroup)) * c) =
      ∑ x ∈ Tf, ψ (Quotient.out x * c) := by
    refine Finset.sum_equiv (Equiv.addRight ((z₀ : K) : K ⧸ R.toAddSubgroup)) ?_ ?_
    · intro x
      show x ∈ Tf ↔ x + ((z₀ : K) : K ⧸ R.toAddSubgroup) ∈ Tf
      rw [hTf, hTf, hx, mem_out hRP, P.add_mem_cancel_right hz]
    · intro x _
      rfl
  have hv : ∀ x : K ⧸ R.toAddSubgroup,
      ψ (Quotient.out (x + ((z₀ : K) : K ⧸ R.toAddSubgroup)) * c) =
        ψ (Quotient.out x * c) * ψ (z₀ * c) := by
    intro x
    rw [hx, psi_out hψ hc, add_mul, AddChar.map_add_eq_mul]
  simp only [hv] at hs
  rw [← Finset.sum_mul] at hs
  have h0 : (∑ x ∈ Tf, ψ (Quotient.out x * c)) * (ψ (z₀ * c) - 1) = 0 := by
    rw [mul_sub, hs, mul_one, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

end Sum

section Parseval

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

/- English proof (translation)
Introduce `a ha l hl`. Conclude with `psi_R hL (R.mul_mem ha (hle hl))`.
-/
theorem R_le_perp (hL : LocalDatum K R ψ) {L₁ : AddSubgroup K} (hle : L₁ ≤ R.toAddSubgroup) :
    R.toAddSubgroup ≤ perp ψ L₁ := by
  intro a ha l hl
  exact psi_R hL (R.mul_mem ha (hle hl))

/- English proof (translation)
Establish `h1 : R.toAddSubgroup.relIndex L₁ = 1` using `AddSubgroup.relIndex_eq_one.mpr hle`. Establish `h2 : (perp ψ L₁).relIndex R.toAddSubgroup = 1` using `AddSubgroup.relIndex_eq_one.mpr (R_le_perp hL hle)`. Establish `h3` using `reps_card _ _ B hB`. Unfold `volL at hvol`. Rewrite `hvol` using `[h1, h2, h3]`.

Establish `hB0 : (B.card : ℝ) ≠ 0`. Introduce `h0`. Rewrite `hvol` using `[h0]`. Simplify using `at hvol`. Establish `: ((R.toAddSubgroup.relIndex (perp ψ L₁) : ℕ) : ℝ) = (B.card : ℝ)`.

Clear denominators, using `at hvol` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.
-/
theorem card_eq (hL : LocalDatum K R ψ) {L₁ : AddSubgroup K} (hle : L₁ ≤ R.toAddSubgroup)
    (B : Finset K) (hB : IsReps B R.toAddSubgroup L₁)
    (hvol : volL R L₁ * volL R (perp ψ L₁) = 1) :
    R.toAddSubgroup.relIndex (perp ψ L₁) = B.card := by
  have h1 : R.toAddSubgroup.relIndex L₁ = 1 := AddSubgroup.relIndex_eq_one.mpr hle
  have h2 : (perp ψ L₁).relIndex R.toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr (R_le_perp hL hle)
  have h3 := reps_card _ _ B hB
  unfold volL at hvol
  rw [h1, h2, h3] at hvol
  have hB0 : (B.card : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hvol
    simp at hvol
  have : ((R.toAddSubgroup.relIndex (perp ψ L₁) : ℕ) : ℝ) = (B.card : ℝ) := by
    field_simp at hvol
    linarith
  exact_mod_cast this

open Classical in
/- English proof (translation)
Establish `hψ : ∀ r ∈ R, ψ r = 1` using `fun r hr => psi_R hL hr`. Establish `hRP` using `R_le_perp hL hle`. Establish `hcardT` using `card_alt hRP`. Establish `hTfin : {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ perp ψ L₁}.Finite`. Establish `: Finite {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ perp ψ L₁}` using `Nat.finite_of_card_ne_zero (by rw [hcardT]; exact hfin)`.

Conclude with `Set.toFinite _`. Use `set Tf := hTfin.toFinset with hTfdef`. Establish `hTf : ∀ x, x ∈ Tf ↔ Quotient.out x ∈ perp ψ L₁`. Introduce `x`. Rewrite using `[hTfdef, Set.Finite.mem_toFinset]`.

Both sides reduce to the same expression. Establish `hTcard : Tf.card = B.card`. Rewrite using `[← card_eq hL hle B hB hvol, ← hcardT, Nat.card_eq_card_finite_toFinset hTfin]`. Establish `hB0 : (B.card : ℂ) ≠ 0`. Rewrite using `[← hTcard, ← Nat.card_eq_card_finite_toFinset hTfin, hcardT]`.

Conclude with `hfin` after adjusting the coercions. Establish `hO : ∀ b ∈ B, ∀ b' ∈ B, ∑ x ∈ Tf, ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) = if b = b' then (B.card : ℂ) else 0`. Introduce `b hb b' hb'`. Establish `e : ∀ x : K ⧸ R.toAddSubgroup, ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) = ψ (Quotient.out x * (b' - b))`. Introduce `x`.

Rewrite using `[hL.unitary, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Distinguish the cases in `hbb : b = b'`.

Substitute `hbb` using the available equality. Rewrite using `[if_pos rfl]`. Simplify using `[hTcard]`. Rewrite using `[if_neg hbb]`. Establish `hc : b' - b ∈ R` using `R.sub_mem (hB.1 b' hb') (hB.1 b hb)`.

Establish `hnot : b' - b ∉ perp ψ (perp ψ L₁)`. Rewrite using `[hpp]`. Introduce `hmem`. Take `⟨a, _, ha⟩` from `hB.2 b' (hB.1 b' hb')`. Establish `e1 : b = a` using `ha b ⟨hb, hmem⟩`.

Establish `e2 : b' = a` using `ha b' ⟨hb', by rw [sub_self]; exact L₁.zero_mem⟩`. Conclude with `hbb (e1.trans e2.symm)`. Establish `: ∃ z₀ ∈ perp ψ L₁, ψ ((b' - b) * z₀) ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hnot hcon`. Take `⟨z₀, hz₀, hne⟩` from `this`. Rewrite `hne` using `[mul_comm]`. Conclude with `orth hψ hRP Tf hTf hc hz₀ hne`. Establish `hS : ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (Quotient.out x : K) ∈ perp ψ L₁ then thx R ψ m cr A B τ (Quotient.out x) h h' else 0) = ∑ x ∈ Tf, thx R ψ m cr A B τ (Quotient.out x) h h'`.

Rewrite using `[finsum_eq_sum_of_support_subset (s := Tf)]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[if_pos ((hTf x).mp hx)]`. Introduce `x hx`. Rewrite using `[Finset.mem_coe, hTf]`.

Assume the negation of the conclusion as `hcon`. Conclude with `hx (if_neg hcon)`. Rewrite using `[hS]`. Unfold `thx`. Rewrite using `[← Finset.mul_sum, Finset.sum_comm, mul_inv, mul_assoc, Finset.mul_sum (a := (B.card : ℂ)⁻¹)]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Establish `h1 : ∀ b ∈ B, ∑ x ∈ Tf, ∑ b' ∈ B, ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = (B.card : ℂ) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b))`. Introduce `b hb`.

Rewrite using `[Finset.sum_comm]`. Establish `h2 : ∀ b' ∈ B, ∑ x ∈ Tf, ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = if b = b' then (B.card : ℂ) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) else 0`. Introduce `b' hb'`. Rewrite using `[← Finset.sum_mul, hO b hb b' hb']`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[Finset.sum_congr rfl h2, Finset.sum_ite_eq, if_pos hb]`. Rewrite using `[Finset.sum_congr rfl h1, ← Finset.mul_sum, ← mul_assoc]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem thxSum_core (hL : LocalDatum K R ψ) {L₁ : AddSubgroup K} (hle : L₁ ≤ R.toAddSubgroup)
    (A B : Finset K) (hB : IsReps B R.toAddSubgroup L₁) (hpp : perp ψ (perp ψ L₁) = L₁)
    (hfin : R.toAddSubgroup.relIndex (perp ψ L₁) ≠ 0)
    (hvol : volL R L₁ * volL R (perp ψ L₁) = 1) (m : ℕ) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (h h' : Point K) :
    ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (Quotient.out x : K) ∈ perp ψ L₁ then
        thx R ψ m cr A B τ (Quotient.out x) h h' else 0) =
      ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ ρ ∈ A, ∑ b ∈ B,
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)) := by
  classical
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => psi_R hL hr
  have hRP := R_le_perp hL hle
  have hcardT := card_alt hRP
  have hTfin : {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ perp ψ L₁}.Finite := by
    have : Finite {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ perp ψ L₁} :=
      Nat.finite_of_card_ne_zero (by rw [hcardT]; exact hfin)
    exact Set.toFinite _
  set Tf := hTfin.toFinset with hTfdef
  have hTf : ∀ x, x ∈ Tf ↔ Quotient.out x ∈ perp ψ L₁ := by
    intro x; rw [hTfdef, Set.Finite.mem_toFinset]; rfl
  have hTcard : Tf.card = B.card := by
    rw [← card_eq hL hle B hB hvol, ← hcardT, Nat.card_eq_card_finite_toFinset hTfin]
  have hB0 : (B.card : ℂ) ≠ 0 := by
    rw [← hTcard, ← Nat.card_eq_card_finite_toFinset hTfin, hcardT]
    exact_mod_cast hfin

  have hO : ∀ b ∈ B, ∀ b' ∈ B, ∑ x ∈ Tf,
      ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) =
        if b = b' then (B.card : ℂ) else 0 := by
    intro b hb b' hb'
    have e : ∀ x : K ⧸ R.toAddSubgroup,
        ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) =
          ψ (Quotient.out x * (b' - b)) := by
      intro x
      rw [hL.unitary, ← AddChar.map_add_eq_mul]
      congr 1; ring
    simp only [e]
    by_cases hbb : b = b'
    · subst hbb
      rw [if_pos rfl]
      simp [hTcard]
    · rw [if_neg hbb]
      have hc : b' - b ∈ R := R.sub_mem (hB.1 b' hb') (hB.1 b hb)
      have hnot : b' - b ∉ perp ψ (perp ψ L₁) := by
        rw [hpp]
        intro hmem
        obtain ⟨a, _, ha⟩ := hB.2 b' (hB.1 b' hb')
        have e1 : b = a := ha b ⟨hb, hmem⟩
        have e2 : b' = a := ha b' ⟨hb', by rw [sub_self]; exact L₁.zero_mem⟩
        exact hbb (e1.trans e2.symm)
      have : ∃ z₀ ∈ perp ψ L₁, ψ ((b' - b) * z₀) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hnot hcon
      obtain ⟨z₀, hz₀, hne⟩ := this
      rw [mul_comm] at hne
      exact orth hψ hRP Tf hTf hc hz₀ hne
  have hS : ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (Quotient.out x : K) ∈ perp ψ L₁ then
        thx R ψ m cr A B τ (Quotient.out x) h h' else 0) =
      ∑ x ∈ Tf, thx R ψ m cr A B τ (Quotient.out x) h h' := by
    rw [finsum_eq_sum_of_support_subset (s := Tf)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [if_pos ((hTf x).mp hx)]
    · intro x hx
      rw [Finset.mem_coe, hTf]
      by_contra hcon
      exact hx (if_neg hcon)
  rw [hS]
  unfold thx
  rw [← Finset.mul_sum, Finset.sum_comm, mul_inv, mul_assoc, Finset.mul_sum (a := (B.card : ℂ)⁻¹)]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ b ∈ B, ∑ x ∈ Tf, ∑ b' ∈ B,
      ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) *
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) =
      (B.card : ℂ) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)) := by
    intro b hb
    rw [Finset.sum_comm]
    have h2 : ∀ b' ∈ B, ∑ x ∈ Tf,
        ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) *
          uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) =
        if b = b' then (B.card : ℂ) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b'))
          else 0 := by
      intro b' hb'
      rw [← Finset.sum_mul, hO b hb b' hb']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq, if_pos hb]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← mul_assoc]
  congr 1
  field_simp

end Parseval

end AveragedKernelSums

open AveragedKernelSums

/- English proof (translation)
Introduce `hCut hKG hN1 hMM K _ _ _ R ψ hL m n₀ F A B τ cr hF hcr hB`. Conclude with `⟨fun z r hr => thx_periodic hL m A B τ cr hB z r hr, fun z => thx_psd (fun F' hF' m cr hcr => (hCut hKG hN1 hMM K R ψ hL m cr Set.univ F' hcr hF').1) m n₀ F A B τ cr hF hcr z⟩`.
-/
theorem averaged_kernel_periodic_psd : Formalism.FourierDecayAlt.A6.ThxBasic := by
  intro hCut hKG hN1 hMM K _ _ _ R ψ hL m n₀ F A B τ cr hF hcr hB
  exact ⟨fun z r hr => thx_periodic hL m A B τ cr hB z r hr, fun z =>
    thx_psd (fun F' hF' m cr hcr => (hCut hKG hN1 hMM K R ψ hL m cr Set.univ F' hcr hF').1)
      m n₀ F A B τ cr hF hcr z⟩

/- English proof (translation)
Introduce `_ _ hPL hLF _ _ _ _ _ K _ _ _ R ψ hL hchar m s n₀ F Om Lc D τ cr _ _ h _ h' _`. Take `⟨hlat, hpp, hvol⟩` from `hPL K R ψ hL hchar D.L₁ D.lat₁`. Conclude with `thxSum_core hL D.le₁ D.A D.B D.repsB hpp (hLF K (perp ψ D.L₁) R.toAddSubgroup hlat ⟨hL.isOpen, hL.isCompact⟩) hvol m τ cr h h'`.
-/
theorem averaged_kernel_parseval : Formalism.FourierDecayAlt.A6.ThxSum := by
  intro _ _ hPL hLF _ _ _ _ _ K _ _ _ R ψ hL hchar m s n₀ F Om Lc D τ cr _ _ h _ h' _
  obtain ⟨hlat, hpp, hvol⟩ := hPL K R ψ hL hchar D.L₁ D.lat₁
  exact thxSum_core hL D.le₁ D.A D.B D.repsB hpp
    (hLF K (perp ψ D.L₁) R.toAddSubgroup hlat ⟨hL.isOpen, hL.isCompact⟩) hvol m τ cr h h'

/- English proof (translation)
Introduce `hSup K _ _ _ R ψ hL s F hs` and use `supportModule_of hSup K R ψ hL s F hs`.
-/
theorem finite_family_truncation_module : Formalism.FourierDecayAlt.A6.SupportModule :=
  fun hSup K _ _ _ R ψ hL s F hs => supportModule_of hSup K R ψ hL s F hs

/- English proof (translation)
Introduce `_ _ _ _ R _ _ h hh` and use `A5x6.cSize_glr R h hh`.
-/
theorem head_size_one_in_GL : Formalism.FourierDecayAlt.A6.CSizeOne :=
  fun _ _ _ _ R _ _ h hh => A5x6.cSize_glr R h hh

/- English proof (translation)
Introduce `aAvg aGH aSt aGP aG aGK aGI aTO aStep`. Introduce `hMS hPO hON hPG hGR hEB hPC hBS hLF hILR hIKR hVS hPL hCM hPD hLC hMLC hSU hSM' hRF hRS hEx`. Introduce `hHD hGM hGIn hGAS`. Introduce `hNS hML hOR hOI hHR hKB hKH hShU hShS hCS hRC hSN hPhD hLoc hCV hXV hCA hUG hUN hCP hUB hAD hCN hTL`. Introduce `hTB hTS hSM hC1 hMM hIF hKG hKBD hNSup`.

Establish `hAB : AvgBound` using `aAvg hMS hPO hON`. Establish `hGH : GaussHess` using `aGH hGM hGIn hHD hMM hVS`. Establish `hSP : StationaryPhase` using `aSt hNS hML hIKR hMM hRF hLC hPL hMLC hOI hVS hRS hSM' hGAS hLF`. Establish `hGP : GermPhi` using `aGP hOR hSP hOI hMM`. Establish `hG : Germ` using `aG hHR hGP`.

Establish `hGK : GermKernel` using `aGK hG hKB hIF hRF`. Introduce `hA2 hN1`. Establish `hGI : GermIdentity` using `aGI hGH hGK hKH hA2.2 hMM hRF hShU hShS hCS hRC hSN hPhD hLoc hMLC hILR hCV hXV`. Establish `hTO : ThOm` using `aTO hGI hAD hLoc hKH hMLC hLC hLF hShU hSU hUG hUN hCP hUB hCA hMM hKG hKBD hGR hAB hPG hPD hPL hCM hCN hTL hTB hTS`. Conclude with `aStep hTO hSM hNSup hC1 hEx hLF hEB hPC hBS hA2 hN1`.
-/
theorem induction_from_assembled_pieces : Formalism.FourierDecayAlt.A6.ThetaExistenceInductiveFromPieces := by
  intro aAvg aGH aSt aGP aG aGK aGI aTO aStep
  intro hMS hPO hON hPG hGR hEB hPC hBS hLF hILR hIKR hVS hPL hCM hPD hLC hMLC hSU hSM' hRF hRS hEx
  intro hHD hGM hGIn hGAS
  intro hNS hML hOR hOI hHR hKB hKH hShU hShS hCS hRC hSN hPhD hLoc hCV hXV hCA hUG hUN hCP hUB hAD
    hCN hTL
  intro hTB hTS hSM hC1 hMM hIF hKG hKBD hNSup
  have hAB : AvgBound := aAvg hMS hPO hON
  have hGH : GaussHess := aGH hGM hGIn hHD hMM hVS
  have hSP : StationaryPhase :=
    aSt hNS hML hIKR hMM hRF hLC hPL hMLC hOI hVS hRS hSM' hGAS hLF
  have hGP : GermPhi := aGP hOR hSP hOI hMM
  have hG : Germ := aG hHR hGP
  have hGK : GermKernel := aGK hG hKB hIF hRF
  intro hA2 hN1
  have hGI : GermIdentity :=
    aGI hGH hGK hKH hA2.2 hMM hRF hShU hShS hCS hRC hSN hPhD hLoc hMLC hILR hCV hXV
  have hTO : ThOm := aTO hGI hAD hLoc hKH hMLC hLC hLF hShU hSU hUG hUN hCP hUB hCA hMM hKG hKBD
    hGR hAB hPG hPD hPL hCM hCN hTL hTB hTS
  exact aStep hTO hSM hNSup hC1 hEx hLF hEB hPC hBS hA2 hN1

end Formalism.FourierDecayAlt.P
