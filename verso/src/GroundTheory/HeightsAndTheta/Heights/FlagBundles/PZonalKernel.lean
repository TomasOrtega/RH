import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Real
open scoped InnerProductSpace

/- English proof (translation)
Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[circleMap, Complex.exp_re, Complex.exp_im]`. Use polynomial arithmetic with `[Real.sin_sq_add_cos_sq φ]`.
-/
theorem norm_circleMap_sub_ofReal_sq (r φ : ℝ) :
    ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos φ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_re, Complex.exp_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

/- English proof (translation)
Introduce `c₁ h₁ c₂ h₂ hne`. Take `⟨h₁l, h₁u⟩` from `h₁`. Take `⟨h₂l, h₂u⟩` from `h₂`. Establish `hs₁ : Real.sqrt (1 - c₁ ^ 2) ^ 2 = 1 - c₁ ^ 2` using `Real.sq_sqrt (by nlinarith)`. Establish `hs₂ : Real.sqrt (1 - c₂ ^ 2) ^ 2 = 1 - c₂ ^ 2` using `Real.sq_sqrt (by nlinarith)`.

Use `set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) with hBdef`. Use `set A := 1 - c₁ * c₂ with hAdef`. Use `set D := |c₁ - c₂| with hDdef`. Establish `hD : 0 < D` using `abs_pos.mpr (sub_ne_zero.mpr hne)`. Establish `hA : 0 ≤ A` using `by nlinarith`.

Establish `hB : 0 ≤ B` using `mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)`. Establish `hABD : A ^ 2 = B ^ 2 + D ^ 2`. Rewrite using `[hBdef, mul_pow, hs₁, hs₂, hDdef, sq_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAD : 0 < A + D` using `by linarith`.

Use `set r := B / (A + D) with hrdef`. Establish `hr0 : 0 ≤ r` using `div_nonneg hB hAD.le`. Establish `hBlt : B < A + D` using `by nlinarith`. Establish `hr1 : r < 1` using `(div_lt_one hAD).mpr hBlt`. Establish `key : ∀ φ : ℝ, kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = (1 / 2) * Real.log ((A + D) / 4) + Real.log ‖circleMap 0 1 φ - (r : ℂ)‖`.

Introduce `φ`. Establish `hinner : ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = c₁ * c₂ + B * Real.cos φ`. Simplify using `[spherePoint, PiLp.inner_apply, Fin.sum_univ_three, hBdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne0 : ‖circleMap 0 1 φ - (r : ℂ)‖ ≠ 0`.

Rewrite using `[norm_ne_zero_iff, sub_ne_zero]`. Introduce `h`. Use `congrArg norm h` as an intermediate fact. Rewrite `this` using `[norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]`. Evaluate the numerical expressions using `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfac : (1 - (c₁ * c₂ + B * Real.cos φ)) / 2 = (A + D) / 4 * ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2`. Rewrite using `[norm_circleMap_sub_ofReal_sq, hrdef]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(2 : ℝ) * hABD`.

Rewrite using `[kernelL, hinner, hfac, Real.log_mul (by positivity) (pow_ne_zero 2 hne0), Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [key]`. Establish `hint : IntervalIntegrable (fun φ : ℝ => Real.log ‖circleMap 0 1 φ - (r : ℂ)‖) MeasureTheory.volume 0 (2 * π)` using `circleIntegrable_log_norm_sub_const (a := (r : ℂ)) (c := 0) 1`.

Rewrite using `[intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const]`. Establish `havg` using `circleAverage_log_norm_sub_const₀ (a := (r : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)`. Rewrite `havg` using `[circleAverage_def, smul_eq_mul]`. Establish `hpi : (2 * π) ≠ 0` using `by positivity`. Establish `hsum : A + D = (1 + max c₁ c₂) * (1 - min c₁ c₂)`.

Break down `le_total c₁ c₂ with h | h` into its components or cases. Rewrite using `[max_eq_right h, min_eq_left h, hDdef, abs_of_nonpos (by linarith), hAdef]; ring`. Rewrite using `[max_eq_left h, min_eq_right h, hDdef, abs_of_nonneg (by linarith), hAdef]; ring`. Rewrite using `[zonalKernel, ← hsum, mul_add, havg, smul_eq_mul, sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ZonalKernel.proof : ZonalKernel.Statement := by
  intro c₁ h₁ c₂ h₂ hne
  obtain ⟨h₁l, h₁u⟩ := h₁
  obtain ⟨h₂l, h₂u⟩ := h₂
  have hs₁ : Real.sqrt (1 - c₁ ^ 2) ^ 2 = 1 - c₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs₂ : Real.sqrt (1 - c₂ ^ 2) ^ 2 = 1 - c₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) with hBdef
  set A := 1 - c₁ * c₂ with hAdef
  set D := |c₁ - c₂| with hDdef
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hA : 0 ≤ A := by nlinarith
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hABD : A ^ 2 = B ^ 2 + D ^ 2 := by
    rw [hBdef, mul_pow, hs₁, hs₂, hDdef, sq_abs]; ring
  have hAD : 0 < A + D := by linarith
  set r := B / (A + D) with hrdef
  have hr0 : 0 ≤ r := div_nonneg hB hAD.le
  have hBlt : B < A + D := by nlinarith
  have hr1 : r < 1 := (div_lt_one hAD).mpr hBlt
  have key : ∀ φ : ℝ, kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ =
      (1 / 2) * Real.log ((A + D) / 4) + Real.log ‖circleMap 0 1 φ - (r : ℂ)‖ := by
    intro φ
    have hinner : ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = c₁ * c₂ + B * Real.cos φ := by
      simp [spherePoint, PiLp.inner_apply, Fin.sum_univ_three, hBdef]
      ring
    have hne0 : ‖circleMap 0 1 φ - (r : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h
      have := congrArg norm h
      rw [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
      norm_num at this
      linarith
    have hfac : (1 - (c₁ * c₂ + B * Real.cos φ)) / 2 =
        (A + D) / 4 * ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 := by
      rw [norm_circleMap_sub_ofReal_sq, hrdef]
      field_simp
      linear_combination (2 : ℝ) * hABD
    rw [kernelL, hinner, hfac, Real.log_mul (by positivity) (pow_ne_zero 2 hne0), Real.log_pow]
    push_cast
    ring
  simp only [key]
  have hint : IntervalIntegrable (fun φ : ℝ => Real.log ‖circleMap 0 1 φ - (r : ℂ)‖)
      MeasureTheory.volume 0 (2 * π) := circleIntegrable_log_norm_sub_const (a := (r : ℂ)) (c := 0) 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const]
  have havg := circleAverage_log_norm_sub_const₀ (a := (r : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  rw [circleAverage_def, smul_eq_mul] at havg
  have hpi : (2 * π) ≠ 0 := by positivity
  have hsum : A + D = (1 + max c₁ c₂) * (1 - min c₁ c₂) := by
    rcases le_total c₁ c₂ with h | h
    · rw [max_eq_right h, min_eq_left h, hDdef, abs_of_nonpos (by linarith), hAdef]; ring
    · rw [max_eq_left h, min_eq_right h, hDdef, abs_of_nonneg (by linarith), hAdef]; ring
  rw [zonalKernel, ← hsum, mul_add, havg, smul_eq_mul, sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi]
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
