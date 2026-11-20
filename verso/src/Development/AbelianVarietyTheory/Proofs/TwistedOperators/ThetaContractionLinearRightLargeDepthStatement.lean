import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearRightLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConLinR.contrLin_one_big` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaContractionLinearRightLargeDepth.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.thetaContraction_linear_right_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 1 := by
  first | exact @GlobalTheory.ConLinR.contrLin_one_big | exact GlobalTheory.ConLinR.contrLin_one_big | (intros; apply GlobalTheory.ConLinR.contrLin_one_big <;> assumption)
