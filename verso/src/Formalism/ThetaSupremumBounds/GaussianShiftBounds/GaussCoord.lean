import Mathlib
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.BlockIntegralOf
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.HeightsoundOf

open Finset MeasureTheory
open scoped ComplexConjugate Real

namespace Formalism.DimensionVariation

/- English proof (translation)
Establish `hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2`. Introduce `z`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `z`. Use `show Real.exp (-(c * ‖z‖ ^ 2)) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)`. Rewrite using `[← Real.exp_add, hsq]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫ p : ℝ × ℝ, Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by`. Conclude with `Complex.volume_preserving_equiv_real_prod.integral_comp' (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))`. Use `_ = (∫ x : ℝ, Real.exp (-c * x ^ 2)) * ∫ y : ℝ, Real.exp (-c * y ^ 2) := integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2))`. Use `_ = π / c := by`.

Rewrite using `[integral_gaussian]`. Conclude with `Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)`.
-/
private theorem integral_complex_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = π / c := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2))
      = ∫ z : ℂ, (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
          (Complex.measurableEquivRealProd z) := by
        congr 1
        funext z
        show Real.exp (-(c * ‖z‖ ^ 2)) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)
        rw [← Real.exp_add, hsq]
        congr 1
        ring
    _ = ∫ p : ℝ × ℝ, Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
        exact Complex.volume_preserving_equiv_real_prod.integral_comp'
          (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
    _ = (∫ x : ℝ, Real.exp (-c * x ^ 2)) * ∫ y : ℝ, Real.exp (-c * y ^ 2) :=
        integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2))
    _ = π / c := by
        rw [integral_gaussian]
        exact Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)

/- English proof (translation)
Introduce `κ hκ b hb`. Establish `hint_r : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `u`.

Rewrite using `[← Finset.sum_neg_distrib, Real.exp_sum]`. Use `_ = ∏ x, ∫ z : ℂ, Real.exp (-(b x * ‖z‖ ^ 2)) := by`. Conclude with `MeasureTheory.integral_fintype_prod_volume_eq_prod (fun x (z : ℂ) => Real.exp (-(b x * ‖z‖ ^ 2)))`. Use `_ = ∏ x, π / b x := Finset.prod_congr rfl fun x _ => integral_complex_exp_neg_mul_sq_norm (hb x)`. Use `⟨?_, hint_r⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hni`. Establish `h0 : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = 0` using `integral_undef hni`. Rewrite `h0` using `[hint_r]`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun x _ => div_ne_zero Real.pi_ne_zero (hb x).ne') h0`.
-/
theorem gaussianIntegralDiagonal : GaussCoord := by
  intro κ hκ b hb
  have hint_r : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x := by
    calc ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2)
        = ∫ u : κ → ℂ, ∏ x, Real.exp (-(b x * ‖u x‖ ^ 2)) := by
          congr 1
          funext u
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ = ∏ x, ∫ z : ℂ, Real.exp (-(b x * ‖z‖ ^ 2)) := by
          exact MeasureTheory.integral_fintype_prod_volume_eq_prod
            (fun x (z : ℂ) => Real.exp (-(b x * ‖z‖ ^ 2)))
      _ = ∏ x, π / b x :=
          Finset.prod_congr rfl fun x _ => integral_complex_exp_neg_mul_sq_norm (hb x)
  refine ⟨?_, hint_r⟩
  by_contra hni
  have h0 : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = 0 := integral_undef hni
  rw [hint_r] at h0
  exact (Finset.prod_ne_zero_iff.mpr fun x _ => div_ne_zero Real.pi_ne_zero (hb x).ne') h0

/- English proof (translation)
The claim follows from `blockIntegral_of gaussianIntegralDiagonal`.
-/
theorem blockIntegralBound : BlockIntegral :=
  blockIntegral_of gaussianIntegralDiagonal

/- English proof (translation)
The claim follows from `blockBound_of hF blockIntegralBound`.
-/
theorem blockBound_of_fockJet (hF : FockJet) : BlockBound :=
  blockBound_of hF blockIntegralBound

end Formalism.DimensionVariation
