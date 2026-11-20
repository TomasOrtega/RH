import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DetHT.testPtSt | exact GlobalTheory.DetHT.testPtSt | (intros; apply GlobalTheory.DetHT.testPtSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.TestPointStatement : TestPtSt := by
  first | exact @GlobalTheory.DetHT.testPtSt | exact GlobalTheory.DetHT.testPtSt | (intros; apply GlobalTheory.DetHT.testPtSt <;> assumption)
