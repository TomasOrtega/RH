import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | exact GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | (intros; apply GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.logarithm_sum_integral_additive : AddSt := by
  first | exact @GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | exact GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | (intros; apply GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality <;> assumption)
