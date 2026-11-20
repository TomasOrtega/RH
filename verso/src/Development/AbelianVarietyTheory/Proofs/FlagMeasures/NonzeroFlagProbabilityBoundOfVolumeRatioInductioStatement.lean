import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNonzeroFlagProbabilityBoundOfVolumeRatioInductio.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction : VolumeStep → NonzeroFlagBound := by
  first | exact @GlobalTheory.NonzeroFlag.nonzeroFlagBound | exact GlobalTheory.NonzeroFlag.nonzeroFlagBound | (intros; apply GlobalTheory.NonzeroFlag.nonzeroFlagBound <;> assumption)
