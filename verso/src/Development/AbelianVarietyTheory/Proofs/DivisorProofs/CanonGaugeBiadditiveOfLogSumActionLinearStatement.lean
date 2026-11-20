import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCanonGaugeBiadditiveOfLogSumActionLinear.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear : AddSt → ActSt → BiaddSt := by
  first | exact @GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | exact GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | (intros; apply GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act <;> assumption)
