import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.IsoTriv.HermRead.finSt_of | exact GlobalTheory.IsoTriv.HermRead.finSt_of | (intros; apply GlobalTheory.IsoTriv.HermRead.finSt_of <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.gaugeHermitianCombination_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FinSt := by
  first | exact @GlobalTheory.IsoTriv.HermRead.finSt_of | exact GlobalTheory.IsoTriv.HermRead.finSt_of | (intros; apply GlobalTheory.IsoTriv.HermRead.finSt_of <;> assumption)
