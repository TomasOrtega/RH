import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Establish `hpi : (2 * Real.pi : ℂ) ≠ 0`. Establish `: (2 * Real.pi : ℝ) ≠ 0` using `by positivity`. Conclude with `this` after adjusting the coercions. Establish `h1 : (2 * Real.pi : ℂ) * (Sz - R) = (V0 - 2 * Real.pi * R) + E`. Rewrite using `[hS]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : I * (V0 - 2 * Real.pi * R) = -(a - b - I * V1)` using `by linear_combination hrect`. Establish `h3 : ‖V0 - 2 * Real.pi * R‖ = ‖a - b - I * V1‖`. Use `congrArg norm h2` as an intermediate fact.

Rewrite `this` using `[norm_mul, Complex.norm_I, one_mul, norm_neg]`. Then use the resulting hypothesis. Establish `h4 : ‖(2 * Real.pi : ℂ) * (Sz - R)‖ = 2 * Real.pi * ‖Sz - R‖`. Rewrite using `[norm_mul]`. Use `congr 1`. Establish `: (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ)` using `by push_cast; rfl`.

Rewrite using `[this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Rewrite using `[← h4, h1]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, Complex.norm_I, one_mul]`.

Use `gcongr`. Conclude with `norm_sub_le _ _`. Use `_ = ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by ring`.
-/
theorem norm_sub_le_of_rectangle_identity (Sz R V0 V1 E a b : ℂ) (hS : Sz = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Sz - R‖ ≤ ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h1 : (2 * Real.pi : ℂ) * (Sz - R) = (V0 - 2 * Real.pi * R) + E := by
    rw [hS]; field_simp; ring
  have h2 : I * (V0 - 2 * Real.pi * R) = -(a - b - I * V1) := by linear_combination hrect
  have h3 : ‖V0 - 2 * Real.pi * R‖ = ‖a - b - I * V1‖ := by
    have := congrArg norm h2
    rwa [norm_mul, Complex.norm_I, one_mul, norm_neg] at this
  have h4 : ‖(2 * Real.pi : ℂ) * (Sz - R)‖ = 2 * Real.pi * ‖Sz - R‖ := by
    rw [norm_mul]
    congr 1
    have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [← h4, h1]
  calc ‖V0 - 2 * Real.pi * R + E‖ ≤ ‖V0 - 2 * Real.pi * R‖ + ‖E‖ := norm_add_le _ _
    _ = ‖a - b - I * V1‖ + ‖E‖ := by rw [h3]
    _ ≤ (‖a‖ + ‖b‖ + ‖V1‖) + ‖E‖ := by
        gcongr
        calc ‖a - b - I * V1‖ ≤ ‖a - b‖ + ‖I * V1‖ := norm_sub_le _ _
          _ ≤ ‖a‖ + ‖b‖ + ‖V1‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]; gcongr; exact norm_sub_le _ _
    _ = ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by ring

/- English proof (translation)
Rewrite using `[intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hf]`.
-/
theorem integral_eq_intervalIntegral_add_compl (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Set.Ioc (-T) T)ᶜ, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hf]

end Formalism.ZF
