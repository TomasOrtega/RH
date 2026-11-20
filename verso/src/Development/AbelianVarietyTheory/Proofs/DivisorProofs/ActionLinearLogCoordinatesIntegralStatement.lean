import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IsoTriv.actSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FActionLinearLogCoordinatesIntegral.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.action_linear_logCoordinates_integral : ActSt := by
  first | exact @GlobalTheory.IsoTriv.actSt | exact GlobalTheory.IsoTriv.actSt | (intros; apply GlobalTheory.IsoTriv.actSt <;> assumption)
