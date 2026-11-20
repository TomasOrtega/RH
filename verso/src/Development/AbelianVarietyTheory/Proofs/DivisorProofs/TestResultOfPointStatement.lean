import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestResultOfPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.testSt_of_ptSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTestResultOfPoint.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.test_result_of_point : PtSt → TestSt := by
  first | exact @GlobalTheory.HalfGeo.testSt_of_ptSt | exact GlobalTheory.HalfGeo.testSt_of_ptSt | (intros; apply GlobalTheory.HalfGeo.testSt_of_ptSt <;> assumption)
