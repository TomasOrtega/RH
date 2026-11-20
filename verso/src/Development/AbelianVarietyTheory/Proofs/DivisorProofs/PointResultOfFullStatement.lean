import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointResultOfFull
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.PointClauses.ptSt_of_fullSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPointResultOfFull.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.point_result_of_full : FullSt → PtSt := by
  first | exact @GlobalTheory.HalfGeo.PointClauses.ptSt_of_fullSt | exact GlobalTheory.HalfGeo.PointClauses.ptSt_of_fullSt | (intros; apply GlobalTheory.HalfGeo.PointClauses.ptSt_of_fullSt <;> assumption)
