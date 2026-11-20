import Mathlib
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.BlockIntegralOf
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.HeightsoundOf

open Finset MeasureTheory
open scoped ComplexConjugate Real

namespace Formalism.DimensionVariation

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Chain the equalities or inequalities of the calculation.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem blockIntegralBound : BlockIntegral :=
  blockIntegral_of gaussianIntegralDiagonal

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem blockBound_of_fockJet (hF : FockJet) : BlockBound :=
  blockBound_of hF blockIntegralBound

end Formalism.DimensionVariation
