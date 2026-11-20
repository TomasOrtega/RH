import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRowAnalyticFactsOfFourSteps.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.rowAnalyticFacts_of_four_steps : StepPinExists → StepVanishPinned → StepLocGenPinnedC → StepThmBPinnedP → StepAnalyticP := by
  first | exact @GlobalTheory.NGRow.stepAnalyticP_of_steps | exact GlobalTheory.NGRow.stepAnalyticP_of_steps | (intros; apply GlobalTheory.NGRow.stepAnalyticP_of_steps <;> assumption)
