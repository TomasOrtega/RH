import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.hasFDerivAt_of_continuous_partials` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHasFDerivAtOfContinuousPartials.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ), (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) → (∀ i, Continuous (d i)) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_partials | exact GlobalTheory.hasFDerivAt_of_continuous_partials | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_partials <;> assumption)
