import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatio
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagMeas.Bound.flagMeasureBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsotropicFlagProbabilityBoundOfVolumeRatio.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio : VolumeStep → FlagMeasureBound := by
  first | exact @GlobalTheory.FlagMeas.Bound.flagMeasureBound | exact GlobalTheory.FlagMeas.Bound.flagMeasureBound | (intros; apply GlobalTheory.FlagMeas.Bound.flagMeasureBound <;> assumption)
