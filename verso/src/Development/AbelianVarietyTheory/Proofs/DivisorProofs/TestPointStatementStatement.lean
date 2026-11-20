import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTestPointStatement.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.TestPointStatement : TestPtSt := by
  first | exact @GlobalTheory.DetHT.testPtSt | exact GlobalTheory.DetHT.testPtSt | (intros; apply GlobalTheory.DetHT.testPtSt <;> assumption)
