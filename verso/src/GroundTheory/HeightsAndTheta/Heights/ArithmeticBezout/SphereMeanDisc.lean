import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanCalc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

/- English proof (translation)
Rewrite using `[integral_fun_norm_addHaar volume (fun r => (Iio (1 : ℝ)).indicator g r), Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]`. Establish `h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y = ∫ y in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun y => y * g y) y`. Use `congr 1`. Use function extensionality and compare the values at `y`. Apply the tactic sequence `by_cases hy : y < 1 <;> simp [indicator, hy]`.

Rewrite using `[h1, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]`. Simplify using `[nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_disc_radial (g : ℝ → ℝ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator g ‖z‖ = 2 * π * ∫ y in (0 : ℝ)..1, y * g y := by
  rw [integral_fun_norm_addHaar volume (fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y =
      ∫ y in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun y => y * g y) y := by
    congr 1
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp [nsmul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[integrable_fun_norm_addHaar volume (f := fun r => (Iio (1 : ℝ)).indicator g r), Complex.finrank_real_complex]`. Establish `h1 : (fun y : ℝ => y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y) = (Iio (1 : ℝ)).indicator (fun y => y * g y)`. Use function extensionality and compare the values at `y`. Apply the tactic sequence `by_cases hy : y < 1 <;> simp [indicator, hy]`. Rewrite using `[h1, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]`.

Conclude with `(hg.integrableOn_Icc).mono_set Ioo_subset_Icc_self`.
-/
theorem integrable_disc_radial (g : ℝ → ℝ) (hg : ContinuousOn (fun y => y * g y) (Icc 0 1)) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator g ‖z‖) := by
  rw [integrable_fun_norm_addHaar volume (f := fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex]
  have h1 : (fun y : ℝ => y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y) =
      (Iio (1 : ℝ)).indicator (fun y => y * g y) := by
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact (hg.integrableOn_Icc).mono_set Ioo_subset_Icc_self

/- English proof (translation)
Rewrite using `[integral_disc_radial, integral_disc_weight]`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_disc_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖ = π / (m + 1) := by
  rw [integral_disc_radial, integral_disc_weight]
  field_simp

/- English proof (translation)
Rewrite using `[integral_disc_radial]`. Establish `h : ∫ y in (0 : ℝ)..1, y * (-log y * (1 - y ^ 2) ^ m) = -∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m`. Rewrite using `[← intervalIntegral.integral_neg]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, integral_disc_log_weight]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_disc_log_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖ =
      π * harmonic (m + 1) / (2 * (m + 1)) := by
  rw [integral_disc_radial]
  have h : ∫ y in (0 : ℝ)..1, y * (-log y * (1 - y ^ 2) ^ m) =
      -∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext y
    ring
  rw [h, integral_disc_log_weight]
  field_simp
  ring

/- English proof (translation)
The claim follows from `integrable_disc_radial _ (by fun_prop)`.
-/
theorem integrable_disc_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) :=
  integrable_disc_radial _ (by fun_prop)

/- English proof (translation)
Apply `integrable_disc_radial` to reduce the goal to its premises. Establish `: (fun y : ℝ => y * (-log y * (1 - y ^ 2) ^ m)) = fun y => -(y * log y) * (1 - y ^ 2) ^ m`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `(continuous_mul_log.neg.mul (by fun_prop)).continuousOn`.
-/
theorem integrable_disc_log_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖) := by
  apply integrable_disc_radial
  have : (fun y : ℝ => y * (-log y * (1 - y ^ 2) ^ m)) =
      fun y => -(y * log y) * (1 - y ^ 2) ^ m := by
    funext y; ring
  rw [this]
  exact (continuous_mul_log.neg.mul (by fun_prop)).continuousOn

end SphereMean

end

end GroundTheory.Heights₂.Heights
