import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.pointSt_of_intSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagBundleHermitianLineDegree.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.point_result_of_integrality : IntSt → PointSt := by
  first | exact @GlobalTheory.HalfGeo.pointSt_of_intSt | exact GlobalTheory.HalfGeo.pointSt_of_intSt | (intros; apply GlobalTheory.HalfGeo.pointSt_of_intSt <;> assumption)
