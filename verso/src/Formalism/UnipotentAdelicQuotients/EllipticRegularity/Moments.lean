import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

/- English proof (translation)
Use `set m : ℕ := n + (d + 1) with hm`. Set `A : E d → ℝ` to `fun v => (1 + ‖v‖ ^ 2) ^ m * ‖F v‖ ^ 2`. Set `B : E d → ℝ` to `fun v => (1 + ‖v‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)`. Establish `hAm : Continuous A`. Establish `: Continuous fun v : E d => (1 + ‖v‖ ^ 2)` using `by fun_prop`.

Conclude with `(this.pow m).mul ((continuous_norm.comp hF).pow 2)`. Establish `hA : Integrable A`. Use `⟨hAm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hs` using `h m`. Unfold `nrm om at hs`.

Rewrite using `[HasFiniteIntegral]`. Use `lt_of_le_of_lt (lintegral_mono fun v => le_of_eq ?_) hs` and prove the remaining obligations. Establish `ht0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2` using `by positivity`. Rewrite using `[Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`.

Simplify using `only [A]`. Use `congr 1`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_div, neg_zero, Real.rpow_zero, mul_one]`. Rewrite using `[← Real.rpow_natCast ((1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)), ← Real.rpow_mul ht0, ← Real.rpow_natCast]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : Integrable B`. Apply `integrable_rpow_neg_one_add_norm_sq` to reduce the goal to its premises. Rewrite using `[finrank_euclideanSpace_fin]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(hA.add hB).mono' ((continuous_norm.pow n).mul (continuous_norm.comp hF)).aestronglyMeasurable ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall (fun v => ?_)` and prove the remaining obligations. Establish `ht1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2` using `by nlinarith [sq_nonneg ‖v‖]`. Establish `ht0 : (0 : ℝ) < 1 + ‖v‖ ^ 2` using `by linarith`.

Establish `hBv : B v = ((1 + ‖v‖ ^ 2) ^ (d + 1))⁻¹`. Simplify using `only [B]`. Rewrite using `[show -(2 * ((d : ℝ) + 1)) / 2 = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg ht0.le, Real.rpow_natCast]`. Establish `hAB : A v * B v = (1 + ‖v‖ ^ 2) ^ n * ‖F v‖ ^ 2`. Rewrite using `[hBv]`.

Simplify using `only [A, hm, pow_add]`. Clear the denominators using the available nonvanishing facts. Establish `hx : (‖v‖ ^ n * ‖F v‖) ^ 2 ≤ A v * B v`. Rewrite using `[hAB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]`. Use `gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA0 : 0 ≤ A v` using `by positivity`. Establish `hB0 : 0 ≤ B v` using `by simp only [B]; positivity`. Establish `hx0 : 0 ≤ ‖v‖ ^ n * ‖F v‖` using `by positivity`. Rewrite using `[Real.norm_of_nonneg hx0]`.

Use `show ‖v‖ ^ n * ‖F v‖ ≤ A v + B v`. Use polynomial arithmetic with `[sq_nonneg (A v - B v), mul_nonneg hA0 hB0]`.
-/
theorem moments_integrable_of_nrm {d : ℕ} (F : E d → ℂ) (hF : Continuous F)
    (h : ∀ s : ℕ, nrm (s : ℝ) 0 0 F < ⊤) (n : ℕ) :
    Integrable (fun v : E d => ‖v‖ ^ n * ‖F v‖) := by
  set m : ℕ := n + (d + 1) with hm
  let A : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ m * ‖F v‖ ^ 2
  let B : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)
  have hAm : Continuous A := by
    have : Continuous fun v : E d => (1 + ‖v‖ ^ 2) := by fun_prop
    exact (this.pow m).mul ((continuous_norm.comp hF).pow 2)
  have hA : Integrable A := by
    refine ⟨hAm.aestronglyMeasurable, ?_⟩
    have hs := h m
    unfold nrm om at hs
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (lintegral_mono fun v => le_of_eq ?_) hs
    have ht0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
    rw [Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [A]
    congr 1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_div, neg_zero,
      Real.rpow_zero, mul_one]
    rw [← Real.rpow_natCast ((1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)), ← Real.rpow_mul ht0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hB : Integrable B := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  refine (hA.add hB).mono' ((continuous_norm.pow n).mul (continuous_norm.comp hF)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  have ht1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have ht0 : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by linarith
  have hBv : B v = ((1 + ‖v‖ ^ 2) ^ (d + 1))⁻¹ := by
    simp only [B]
    rw [show -(2 * ((d : ℝ) + 1)) / 2 = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg ht0.le,
      Real.rpow_natCast]
  have hAB : A v * B v = (1 + ‖v‖ ^ 2) ^ n * ‖F v‖ ^ 2 := by
    rw [hBv]
    simp only [A, hm, pow_add]
    field_simp
  have hx : (‖v‖ ^ n * ‖F v‖) ^ 2 ≤ A v * B v := by
    rw [hAB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    gcongr
    linarith
  have hA0 : 0 ≤ A v := by positivity
  have hB0 : 0 ≤ B v := by simp only [B]; positivity
  have hx0 : 0 ≤ ‖v‖ ^ n * ‖F v‖ := by positivity
  rw [Real.norm_of_nonneg hx0]
  show ‖v‖ ^ n * ‖F v‖ ≤ A v + B v
  nlinarith [sq_nonneg (A v - B v), mul_nonneg hA0 hB0]

/- English proof (translation)
Introduce `d g hg hgc hs`. Establish `hgi : Integrable g` using `hg.integrable_of_hasCompactSupport hgc`. Establish `hFc : Continuous (𝓕 g)` using `VectorFourier.fourierIntegral_continuous (L := innerₗ (E d)) Real.continuous_fourierChar (by simpa using continuous_inner) hgi`. Establish `hmom` using `moments_integrable_of_nrm (𝓕 g) hFc hs`. Establish `hFi : Integrable (𝓕 g)`.

Establish `h0` using `hmom 0`. Simplify using `only [pow_zero, one_mul] at h0`. Conclude with `(integrable_norm_iff hFc.aestronglyMeasurable).mp h0`. Establish `hinv` using `hg.fourierInv_fourier_eq hgi hFi`. Establish `hsm : ContDiff ℝ ∞ (𝓕 (𝓕 g))` using `VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ) (μ := volume) (N := ⊤) (f := 𝓕 g) (fun n _ => hmom n)`.

Establish `hg' : g = fun w => 𝓕 (𝓕 g) (-w)` using `by conv_lhs => rw [← hinv]`. Use extensionality with `w`. Conclude with `Real.fourierInv_eq_fourier_neg _ w`. Rewrite using `[hg']`. Conclude with `hsm.comp contDiff_neg`.
-/
theorem smoothOfSobolevAll : MomentsSmooth := by
  intro d g hg hgc hs
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hFc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ (E d)) Real.continuous_fourierChar
      (by simpa using continuous_inner) hgi
  have hmom := moments_integrable_of_nrm (𝓕 g) hFc hs
  have hFi : Integrable (𝓕 g) := by
    have h0 := hmom 0
    simp only [pow_zero, one_mul] at h0
    exact (integrable_norm_iff hFc.aestronglyMeasurable).mp h0
  have hinv := hg.fourierInv_fourier_eq hgi hFi
  have hsm : ContDiff ℝ ∞ (𝓕 (𝓕 g)) :=
    VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ) (μ := volume) (N := ⊤) (f := 𝓕 g)
      (fun n _ => hmom n)
  have hg' : g = fun w => 𝓕 (𝓕 g) (-w) := by
    conv_lhs => rw [← hinv]
    ext w
    exact Real.fourierInv_eq_fourier_neg _ w
  rw [hg']
  exact hsm.comp contDiff_neg

end ZetaZeros.D.EllReg
