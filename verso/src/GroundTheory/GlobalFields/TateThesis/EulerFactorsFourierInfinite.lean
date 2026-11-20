import Mathlib
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInverse
import GroundTheory.GlobalFields.TateThesis.GaussianComplexFourier
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

open NumberField InfinitePlace MeasureTheory Complex ComplexConjugate NumberField.mixedEmbedding
open scoped Real FourierTransform Classical

namespace GroundTheory.Global

noncomputable section

/- English proof (translation)
Break down `(show n = 0 ∨ n = 1 by omega) with rfl | rfl` into its components or cases. Simplify using `only [pow_zero, one_mul]`. Rewrite using `[show (fun t : ℝ ↦ realGaussian t) = realGaussian from rfl, fourier_realGaussian]`. Simplify using `only [pow_one]`. Rewrite using `[show (fun t : ℝ ↦ (t : ℂ) * realGaussian t) = realGaussianOdd from rfl, fourier_realGaussianOdd]`.

Both sides reduce to the same expression.
-/
theorem fourier_pow_mul_realGaussian {n : ℕ} (hn : n < 2) (y : ℝ) :
    𝓕 (fun t : ℝ ↦ (t : ℂ) ^ n * realGaussian t) y = (-I) ^ n * ((y : ℂ) ^ n * realGaussian y) := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · simp only [pow_zero, one_mul]
    rw [show (fun t : ℝ ↦ realGaussian t) = realGaussian from rfl, fourier_realGaussian]
  · simp only [pow_one]
    rw [show (fun t : ℝ ↦ (t : ℂ) * realGaussian t) = realGaussianOdd from rfl,
      fourier_realGaussianOdd]
    rfl

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

/- English proof (translation)
Rewrite using `[infiniteSchwartz_apply, infinitePoly]`. Simplify using `only [complexGaussian, Int.natAbs_neg, realGaussian_eq_ofReal, Finset.prod_mul_distrib]`. Establish `hc : ∀ w : {w // IsComplex w}, (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^ (χ.infiniteWeight w).natAbs = (if 0 ≤ -χ.infiniteWeight w then x.2 w ^ (χ.infiniteWeight w).natAbs else conj (x.2 w) ^ (χ.infiniteWeight w).natAbs)` using `fun w ↦ by`. Distinguish the cases in `h : 0 < χ.infiniteWeight w`. Rewrite using `[if_pos h, if_neg (by omega)]`.

Rewrite using `[if_neg h, if_pos (by omega)]`. Simplify using `only [hc]`. Establish `hexp : ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) = (∏ w : {w // IsReal w}, ((Real.exp (-(π * x.1 w ^ 2)) : ℝ) : ℂ)) * ∏ w : {w // IsComplex w}, Complex.exp (-2 * π * (‖x.2 w‖ : ℂ) ^ 2)`. Establish `e2 : ∀ w : {w // IsComplex w}, Complex.exp (-2 * π * (‖x.2 w‖ : ℂ) ^ 2) = ((Real.exp (-(2 * π * ‖x.2 w‖ ^ 2)) : ℝ) : ℂ)` using `fun w ↦ by`. Rewrite using `[ofReal_exp]`.

Use `push_cast`. Put the polynomial expressions in normal form. Simplify using `only [e2]`. Rewrite using `[← ofReal_prod, ← ofReal_prod, ← ofReal_mul, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]`. Use `congr 2`.

Rewrite using `[mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Apply the tactic sequence `congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by ring`. Rewrite using `[hexp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem infiniteSchwartz_eq_prod (x : mixedSpace K) :
    χ.infiniteSchwartz x =
      (∏ w : {w // IsReal w}, ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs *
        realGaussian (x.1 w)) *
      ∏ w : {w // IsComplex w}, complexGaussian (-χ.infiniteWeight w) (x.2 w) := by
  rw [infiniteSchwartz_apply, infinitePoly]
  simp only [complexGaussian, Int.natAbs_neg, realGaussian_eq_ofReal, Finset.prod_mul_distrib]
  have hc : ∀ w : {w // IsComplex w},
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^ (χ.infiniteWeight w).natAbs =
      (if 0 ≤ -χ.infiniteWeight w then x.2 w ^ (χ.infiniteWeight w).natAbs
        else conj (x.2 w) ^ (χ.infiniteWeight w).natAbs) := fun w ↦ by
    by_cases h : 0 < χ.infiniteWeight w
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  simp only [hc]
  have hexp : ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) =
      (∏ w : {w // IsReal w}, ((Real.exp (-(π * x.1 w ^ 2)) : ℝ) : ℂ)) *
        ∏ w : {w // IsComplex w}, Complex.exp (-2 * π * (‖x.2 w‖ : ℂ) ^ 2) := by
    have e2 : ∀ w : {w // IsComplex w}, Complex.exp (-2 * π * (‖x.2 w‖ : ℂ) ^ 2) =
        ((Real.exp (-(2 * π * ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := fun w ↦ by
      rw [ofReal_exp]; push_cast; ring_nf
    simp only [e2]
    rw [← ofReal_prod, ← ofReal_prod, ← ofReal_mul, ← Real.exp_sum, ← Real.exp_sum,
      ← Real.exp_add]
    congr 2
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by ring
  rw [hexp]
  ring

/- English proof (translation)
Rewrite using `[mixedTraceForm_apply', neg_add, AddChar.map_add_eq_mul, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, addChar_map_finsetSum, addChar_map_finsetSum, Circle.coe_mul]`. Apply the tactic sequence `congr 1 <;> exact map_prod Circle.coeHom _ _`.
-/
theorem fourierChar_neg_mixedTraceForm (x y : mixedSpace K) :
    ((𝐞 (-mixedTraceForm K x y) : Circle) : ℂ) =
      (∏ w : {w // IsReal w}, ((𝐞 (-(x.1 w * y.1 w)) : Circle) : ℂ)) *
        ∏ w : {w // IsComplex w}, ((𝐞 (-(2 * (x.2 w * y.2 w).re)) : Circle) : ℂ) := by
  rw [mixedTraceForm_apply', neg_add, AddChar.map_add_eq_mul, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib, addChar_map_finsetSum, addChar_map_finsetSum, Circle.coe_mul]
  congr 1 <;> exact map_prod Circle.coeHom _ _

/- English proof (translation)
Use `set A : ∀ w : {w // IsReal w}, ℝ → ℂ := fun w t ↦ ((𝐞 (-(t * y.1 w)) : Circle) : ℂ) * ((t : ℂ) ^ (χ.infiniteWeight w).natAbs * realGaussian t)`. Use `set B : ∀ w : {w // IsComplex w}, ℂ → ℂ := fun w z ↦ ((𝐞 (-(2 * (z * y.2 w).re)) : Circle) : ℂ) * complexGaussian (-χ.infiniteWeight w) z`. Establish `hint : ∀ x : mixedSpace K, 𝐞 (-mixedTraceForm K x y) • χ.infiniteSchwartz x = (∏ w, A w (x.1 w)) * ∏ w, B w (x.2 w)`. Introduce `x`. Rewrite using `[Circle.smul_def, smul_eq_mul, fourierChar_neg_mixedTraceForm, infiniteSchwartz_eq_prod]`.

Simplify using `only [A, B, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : ∀ w : {w // IsReal w}, ∫ t, A w t = (-I) ^ (χ.infiniteWeight w).natAbs * ((y.1 w : ℂ) ^ (χ.infiniteWeight w).natAbs * realGaussian (y.1 w))`. Introduce `w`. Establish `hm` using `χ.infiniteWeight_of_isReal w.2`.

Rewrite using `[← fourier_pow_mul_realGaussian (by omega), Real.fourier_real_eq]`. Both sides reduce to the same expression. Establish `hB : ∀ w : {w // IsComplex w}, ∫ z, B w z = (-I) ^ (χ.infiniteWeight w).natAbs * complexGaussian (χ.infiniteWeight w) (y.2 w) / 2`. Introduce `w`. Establish `h` using `congrFun (complexFourier_complexGaussian (-χ.infiniteWeight w)) (y.2 w)`.

Rewrite `h` using `[neg_neg, Int.natAbs_neg, complexFourier, complexPlaceMeasure, integral_smul_measure]`. Simplify using `only [ENNReal.toReal_ofNat, Circle.smul_def, smul_eq_mul] at h`. Rewrite using `[← h]`. Simplify using `only [B, Complex.real_smul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mixedFourier_apply, selfDualMeasure, integral_smul_measure, Measure.volume_eq_prod]`. Simplify using `only [hint]`. Rewrite using `[integral_prod_mul (f := fun a : {w // IsReal w} → ℝ ↦ ∏ w, A w (a w)) (g := fun b : {w // IsComplex w} → ℂ ↦ ∏ w, B w (b w)), integral_fintype_prod_volume_eq_prod, integral_fintype_prod_volume_eq_prod]`. Simplify using `only [hA, hB]`.

Rewrite using `[(χ⁻¹).infiniteSchwartz_eq_prod, prod_eq_prod_mul_prod]`. Establish `hr : ∀ w : {w // IsReal w}, (χ⁻¹).infiniteWeight w = χ.infiniteWeight w` using `fun w ↦ χ.infiniteWeight_inv_of_isReal w.2`. Establish `hc : ∀ w : {w // IsComplex w}, (χ⁻¹).infiniteWeight w = -χ.infiniteWeight w` using `fun w ↦ χ.infiniteWeight_inv_of_isComplex w.2`. Simplify using `only [hr, hc, neg_neg, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Complex.real_smul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]`. Establish `h2 : (2 : ℂ) ^ Fintype.card {w : InfinitePlace K // IsComplex w} ≠ 0` using `pow_ne_zero _ two_ne_zero`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem mixedFourier_infiniteSchwartz (y : mixedSpace K) :
    mixedFourier K χ.infiniteSchwartz y =
      (∏ w, (-I) ^ (χ.infiniteWeight w).natAbs) * (χ⁻¹).infiniteSchwartz y := by
  set A : ∀ w : {w // IsReal w}, ℝ → ℂ := fun w t ↦ ((𝐞 (-(t * y.1 w)) : Circle) : ℂ) *
    ((t : ℂ) ^ (χ.infiniteWeight w).natAbs * realGaussian t)
  set B : ∀ w : {w // IsComplex w}, ℂ → ℂ := fun w z ↦
    ((𝐞 (-(2 * (z * y.2 w).re)) : Circle) : ℂ) * complexGaussian (-χ.infiniteWeight w) z
  have hint : ∀ x : mixedSpace K, 𝐞 (-mixedTraceForm K x y) • χ.infiniteSchwartz x =
      (∏ w, A w (x.1 w)) * ∏ w, B w (x.2 w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, fourierChar_neg_mixedTraceForm, infiniteSchwartz_eq_prod]
    simp only [A, B, Finset.prod_mul_distrib]
    ring
  have hA : ∀ w : {w // IsReal w}, ∫ t, A w t =
      (-I) ^ (χ.infiniteWeight w).natAbs *
        ((y.1 w : ℂ) ^ (χ.infiniteWeight w).natAbs * realGaussian (y.1 w)) := by
    intro w
    have hm := χ.infiniteWeight_of_isReal w.2
    rw [← fourier_pow_mul_realGaussian (by omega), Real.fourier_real_eq]
    rfl
  have hB : ∀ w : {w // IsComplex w}, ∫ z, B w z =
      (-I) ^ (χ.infiniteWeight w).natAbs * complexGaussian (χ.infiniteWeight w) (y.2 w) / 2 := by
    intro w
    have h := congrFun (complexFourier_complexGaussian (-χ.infiniteWeight w)) (y.2 w)
    rw [neg_neg, Int.natAbs_neg, complexFourier, complexPlaceMeasure, integral_smul_measure] at h
    simp only [ENNReal.toReal_ofNat, Circle.smul_def, smul_eq_mul] at h
    rw [← h]
    simp only [B, Complex.real_smul]
    push_cast
    ring
  rw [mixedFourier_apply, selfDualMeasure, integral_smul_measure, Measure.volume_eq_prod]
  simp only [hint]
  rw [integral_prod_mul (f := fun a : {w // IsReal w} → ℝ ↦ ∏ w, A w (a w))
    (g := fun b : {w // IsComplex w} → ℂ ↦ ∏ w, B w (b w)), integral_fintype_prod_volume_eq_prod,
    integral_fintype_prod_volume_eq_prod]
  simp only [hA, hB]
  rw [(χ⁻¹).infiniteSchwartz_eq_prod, prod_eq_prod_mul_prod]
  have hr : ∀ w : {w // IsReal w}, (χ⁻¹).infiniteWeight w = χ.infiniteWeight w := fun w ↦
    χ.infiniteWeight_inv_of_isReal w.2
  have hc : ∀ w : {w // IsComplex w}, (χ⁻¹).infiniteWeight w = -χ.infiniteWeight w := fun w ↦
    χ.infiniteWeight_inv_of_isComplex w.2
  simp only [hr, hc, neg_neg, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Complex.real_smul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have h2 : (2 : ℂ) ^ Fintype.card {w : InfinitePlace K // IsComplex w} ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  field_simp

end HeckeCharacter

end

end GroundTheory.Global
