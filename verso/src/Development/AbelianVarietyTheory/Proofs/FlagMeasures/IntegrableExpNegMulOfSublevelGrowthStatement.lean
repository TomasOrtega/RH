import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowth
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIntegrableExpNegMulOfSublevelGrowth.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d → (∀ x, 0 ≤ d x) → (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b → Integrable (fun x => Real.exp (-(b * d x))) μ := by
  first | exact @GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | (intros; apply GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth <;> assumption)
