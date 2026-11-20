import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMoments
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomTop.jetMoments` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FKernelJetsLevelPlaceIntegralMoments.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.kernelJets_levelPlace_integralMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments := by
  first | exact @GlobalTheory.MomTop.jetMoments | exact GlobalTheory.MomTop.jetMoments | (intros; apply GlobalTheory.MomTop.jetMoments <;> assumption)
