import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilHomGen.homSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHomomorphismResult.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.homomorphism_result : HomSt := by
  first | exact @GlobalTheory.WeilHomGen.homSt | exact GlobalTheory.WeilHomGen.homSt | (intros; apply GlobalTheory.WeilHomGen.homSt <;> assumption)
