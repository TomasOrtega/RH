import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearityResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLinearityResult.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.linearity_result : LinSt := by
  first | exact @GlobalTheory.HalfGeo.linSt | exact GlobalTheory.HalfGeo.linSt | (intros; apply GlobalTheory.HalfGeo.linSt <;> assumption)
