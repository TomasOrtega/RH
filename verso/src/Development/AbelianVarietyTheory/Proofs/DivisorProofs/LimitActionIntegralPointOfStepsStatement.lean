import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLimitActionIntegralPointOfSteps.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.limitActionIntegralPoint_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  first | exact @GlobalTheory.IsoTriv.limPt_of_steps | exact GlobalTheory.IsoTriv.limPt_of_steps | (intros; apply GlobalTheory.IsoTriv.limPt_of_steps <;> assumption)
