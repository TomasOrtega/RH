import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLiftingResult.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.lifting_result : LiftSt := by
  first | exact @GlobalTheory.HalfGeo.liftSt | exact GlobalTheory.HalfGeo.liftSt | (intros; apply GlobalTheory.HalfGeo.liftSt <;> assumption)
