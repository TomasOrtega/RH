import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FSInv

open MeasureTheory

/- English proof (translation)
Introduce `N s hs`. Establish `hc : 0 < s⁻¹` using `inv_pos.2 hs`. Take `⟨hI, hV⟩` from `GroundTheory.Heights₂.Heights.integral_complex_norm_pow_div s⁻¹ hc 0 N`. Establish `hpt : ∀ t : ℂ, ‖t‖ ^ (2 * N) * (1 / (1 + ‖t‖ ^ 2 * s) ^ (N + 2)) = (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0))`. Introduce `t`.

Establish `h1 : 1 + ‖t‖ ^ 2 * s = s * (s⁻¹ + ‖t‖ ^ 2)` using `by field_simp`. Establish `h2 : 0 < s⁻¹ + ‖t‖ ^ 2` using `by positivity`. Rewrite using `[h1, mul_pow, add_zero, inv_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hnn : 0 ≤ᵐ[volume] fun t : ℂ => (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0))` using `Filter.Eventually.of_forall fun t => by positivity`.

Repeatedly rewrite using `[hpt]`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (hI.const_mul _) hnn, integral_const_mul, hV, ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Simplify using `only [Nat.factorial_zero, Nat.cast_one, mul_one, add_zero, zero_add, pow_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]`. Establish `hN : (N.factorial : ℝ) ≠ 0` using `by positivity`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[div_pow, one_pow, show s ^ (N + 2) = s * s ^ (N + 1) by ring]`. Clear the denominators using the available nonvanishing facts.
-/
theorem Radial.proof : Radial.Statement := by
  intro N s hs
  have hc : 0 < s⁻¹ := inv_pos.2 hs
  obtain ⟨hI, hV⟩ := GroundTheory.Heights₂.Heights.integral_complex_norm_pow_div s⁻¹ hc 0 N
  have hpt : ∀ t : ℂ, ‖t‖ ^ (2 * N) * (1 / (1 + ‖t‖ ^ 2 * s) ^ (N + 2)) =
      (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0)) := by
    intro t
    have h1 : 1 + ‖t‖ ^ 2 * s = s * (s⁻¹ + ‖t‖ ^ 2) := by field_simp
    have h2 : 0 < s⁻¹ + ‖t‖ ^ 2 := by positivity
    rw [h1, mul_pow, add_zero, inv_pow]
    field_simp
  have hnn : 0 ≤ᵐ[volume] fun t : ℂ => (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0)) :=
    Filter.Eventually.of_forall fun t => by positivity
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul _) hnn, integral_const_mul, hV,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one, add_zero, zero_add, pow_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [div_pow, one_pow, show s ^ (N + 2) = s * s ^ (N + 1) by ring]
  field_simp

end GroundTheory.Heights₂.Heights.FSInv
