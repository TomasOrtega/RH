import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FColumnInclusionIntegralOfLimitSteps.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  first | exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim | exact GlobalTheory.IsoTriv.Incl.inclSt_of_lim | (intros; apply GlobalTheory.IsoTriv.Incl.inclSt_of_lim <;> assumption)
