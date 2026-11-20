import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySphereVolumeProductRatioAndInvBounds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.sphV_ratio_and_inv_bounds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnitarySphereVolumeProductRatioAndInvBounds.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds : (∀ q j : ℕ, j ≤ q → Real.log (sphV q / sphV (q - j)) ≤ 3.49 * j) ∧ ∀ J : ℕ, 0 < sphV J ∧ (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  first | exact @GlobalTheory.sphV_ratio_and_inv_bounds | exact GlobalTheory.sphV_ratio_and_inv_bounds | (intros; apply GlobalTheory.sphV_ratio_and_inv_bounds <;> assumption)
