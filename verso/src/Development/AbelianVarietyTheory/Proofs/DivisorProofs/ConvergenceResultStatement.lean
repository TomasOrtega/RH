import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvergenceResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.convSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConvergenceResult.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.convergence_result : ConvSt := by
  first | exact @GlobalTheory.HalfGeo.convSt | exact GlobalTheory.HalfGeo.convSt | (intros; apply GlobalTheory.HalfGeo.convSt <;> assumption)
