import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

/- English proof (authored)
Multiply the formula for Sz by 2π and subtract 2πR. The rectangle identity writes the remaining vertical difference, after multiplication by the imaginary unit, as the signed sum of the two horizontal pieces and the other vertical piece. Multiplication by the imaginary unit preserves the norm. Apply the triangle inequality to these three contributions and the tail E.
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

/- English proof (authored)
The whole line is the disjoint union of the interval from −T to T, open at the left end, and its complement. Use additivity of the integral of an integrable function. Since −T ≤ T, the interval integral agrees with the integral over that half-open interval.
-/
theorem integral_eq_intervalIntegral_add_compl (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Set.Ioc (-T) T)ᶜ, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hf]

end Formalism.ZF
