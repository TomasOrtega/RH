import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaKernelModerateGrowthWithSeminorms.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D := by
  first | exact @GlobalTheory.KernelSeminorm.thetaGrowth_onObjects | exact GlobalTheory.KernelSeminorm.thetaGrowth_onObjects | (intros; apply GlobalTheory.KernelSeminorm.thetaGrowth_onObjects <;> assumption)
