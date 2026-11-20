import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.IsoTriv.frameSt_of | exact GlobalTheory.IsoTriv.frameSt_of | (intros; apply GlobalTheory.IsoTriv.frameSt_of <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit : ActSt → UnitSt → FrameSt := by
  first | exact @GlobalTheory.IsoTriv.frameSt_of | exact GlobalTheory.IsoTriv.frameSt_of | (intros; apply GlobalTheory.IsoTriv.frameSt_of <;> assumption)
