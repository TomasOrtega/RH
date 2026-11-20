import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.NGRow.exists_row_level_analytic | exact GlobalTheory.NGRow.exists_row_level_analytic | (intros; apply GlobalTheory.NGRow.exists_row_level_analytic <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps : TieOfCtx → StepChoiceConstantsC → StepAnalyticP → StepAnalyticConstantsP := by
  first | exact @GlobalTheory.NGRow.exists_row_level_analytic | exact GlobalTheory.NGRow.exists_row_level_analytic | (intros; apply GlobalTheory.NGRow.exists_row_level_analytic <;> assumption)
