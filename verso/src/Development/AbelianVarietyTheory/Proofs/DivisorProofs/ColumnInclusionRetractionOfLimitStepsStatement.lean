import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.IsoTriv.retrSt_of | exact GlobalTheory.IsoTriv.retrSt_of | (intros; apply GlobalTheory.IsoTriv.retrSt_of <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.columnInclusionRetraction_of_limitSteps : LimActSt → LimPtSt → InvSt → RetrSt := by
  first | exact @GlobalTheory.IsoTriv.retrSt_of | exact GlobalTheory.IsoTriv.retrSt_of | (intros; apply GlobalTheory.IsoTriv.retrSt_of <;> assumption)
