import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorsResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.GensProof.gens` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeneratorsResult.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.generators_result : GensSt := by
  first | exact @GlobalTheory.HalfGeo.GensProof.gens | exact GlobalTheory.HalfGeo.GensProof.gens | (intros; apply GlobalTheory.HalfGeo.GensProof.gens <;> assumption)
