import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralityResult.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.integrality_result : IntSt := by
  first | exact @GlobalTheory.HalfGeo.IntProof.intSt | exact GlobalTheory.HalfGeo.IntProof.intSt | (intros; apply GlobalTheory.HalfGeo.IntProof.intSt <;> assumption)
