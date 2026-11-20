import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
open Formalism.L2.SG.Pf.MainEqSteps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.stepNormalsG_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNormalCountGenericRow.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.normalCount_genericRow : StepNormalsG := by
  first | exact @GlobalTheory.stepNormalsG_holds | exact GlobalTheory.stepNormalsG_holds | (intros; apply GlobalTheory.stepNormalsG_holds <;> assumption)
