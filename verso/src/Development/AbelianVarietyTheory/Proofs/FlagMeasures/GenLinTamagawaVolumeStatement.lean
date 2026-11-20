import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenLinTamagawaVolume
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagMeas.genLinVolume` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGenLinTamagawaVolume.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.genLin_tamagawa_volume : GenLinVolume := by
  first | exact @GlobalTheory.FlagMeas.genLinVolume | exact GlobalTheory.FlagMeas.genLinVolume | (intros; apply GlobalTheory.FlagMeas.genLinVolume <;> assumption)
