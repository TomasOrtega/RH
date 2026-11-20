import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedSteps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SnPos.stepAnalyticCGP_of_steps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAnalyticConstantGenericBoundOfNormalisedSteps.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → StepAnalyticCGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticCGP_of_steps | exact GlobalTheory.SnPos.stepAnalyticCGP_of_steps | (intros; apply GlobalTheory.SnPos.stepAnalyticCGP_of_steps <;> assumption)
