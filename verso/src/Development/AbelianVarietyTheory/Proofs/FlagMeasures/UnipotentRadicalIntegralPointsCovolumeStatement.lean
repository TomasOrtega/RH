import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIntegralPointsCovolume
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RadCov.radicalCovolume` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnipotentRadicalIntegralPointsCovolume.lean&line=240#L240)
-/
theorem _root_.GlobalTheory.T.unipotentRadical_integral_points_covolume : RadicalCovolume := by
  first | exact @GlobalTheory.RadCov.radicalCovolume | exact GlobalTheory.RadCov.radicalCovolume | (intros; apply GlobalTheory.RadCov.radicalCovolume <;> assumption)
