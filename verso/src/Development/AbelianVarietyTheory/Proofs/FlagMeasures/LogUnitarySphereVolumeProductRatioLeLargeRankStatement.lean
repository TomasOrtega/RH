import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogUnitarySphereVolumeProductRatioLeLargeRank
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SphRatio.log_sphV_ratio_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLogUnitarySphereVolumeProductRatioLeLargeRank.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.log_unitarySphereVolumeProduct_ratio_le_large_rank : ∀ (n p j : ℕ), 18 ≤ n → j ≤ p → p ≤ n → (n : ℝ) - 2 * Real.sqrt n ≤ (p : ℝ) - j → (n : ℝ) / 2 ≤ (p : ℝ) - j → Real.log (sphV p / sphV (p - j)) ≤ j * Real.log (2 * Real.pi) - j * ((n : ℝ) - 2 * Real.sqrt n) * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  first | exact @GlobalTheory.SphRatio.log_sphV_ratio_le | exact GlobalTheory.SphRatio.log_sphV_ratio_le | (intros; apply GlobalTheory.SphRatio.log_sphV_ratio_le <;> assumption)
