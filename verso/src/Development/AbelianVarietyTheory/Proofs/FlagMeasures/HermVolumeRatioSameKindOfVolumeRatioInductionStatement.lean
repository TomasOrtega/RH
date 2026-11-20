import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermVolumeRatioSameKindOfVolumeRatioInduction
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHermVolumeRatioSameKindOfVolumeRatioInduction.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction : VolumeStep → VolumeRatio := by
  first | exact @GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | exact GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep <;> assumption)
