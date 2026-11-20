import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFullResult.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.full_result : FullSt := by
  first | exact @GlobalTheory.HalfGeo.fullSt | exact GlobalTheory.HalfGeo.fullSt | (intros; apply GlobalTheory.HalfGeo.fullSt <;> assumption)
