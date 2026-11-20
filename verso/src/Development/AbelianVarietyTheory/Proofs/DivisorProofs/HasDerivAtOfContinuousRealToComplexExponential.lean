import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousOfMapAdd
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add`. Consider the case `exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add`. Consider the case `(apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add ..)`.
-/
theorem hasDerivAt_of_continuous_additive_to_mul (χ : ℝ → ℂ) (hc : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) (h0 : χ 0 = 1) :
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first
  | exact @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | (apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add ..)

end GlobalTheory
