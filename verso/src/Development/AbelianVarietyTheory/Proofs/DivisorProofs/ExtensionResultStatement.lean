import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.extSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExtensionResult.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.extension_result : ExtSt := by
  first | exact @GlobalTheory.HalfGeo.extSt | exact GlobalTheory.HalfGeo.extSt | (intros; apply GlobalTheory.HalfGeo.extSt <;> assumption)
