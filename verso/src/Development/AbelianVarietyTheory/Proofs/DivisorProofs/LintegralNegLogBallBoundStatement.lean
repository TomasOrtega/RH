import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNegLogBallBound
import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralNegLogBallBound.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.lintegral_neg_log_ball_bound : ∀ {d : ℕ} (a : ReciprocityTheory.L2DbarEstimates.V d) (r : ℝ) (i : Fin d), 0 < r → r ≤ 1 → ∫⁻ w in Metric.ball a r, ENNReal.ofReal (max 0 (-Real.log (‖w i‖ ^ 2))) ≤ ENNReal.ofReal ((Real.pi * r ^ 2) ^ d * (1 - 2 * Real.log (r ^ 2))) := by
  first | exact @GlobalTheory.LogBox.lintegral_posNegLogNormSq_coord_ball_le | exact GlobalTheory.LogBox.lintegral_posNegLogNormSq_coord_ball_le | (intros; apply GlobalTheory.LogBox.lintegral_posNegLogNormSq_coord_ball_le <;> assumption)
