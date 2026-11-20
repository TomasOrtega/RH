import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpectralResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.SpecProof.specSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpectralResult.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.spectral_result : SpecSt := by
  first | exact @GlobalTheory.HalfGeo.SpecProof.specSt | exact GlobalTheory.HalfGeo.SpecProof.specSt | (intros; apply GlobalTheory.HalfGeo.SpecProof.specSt <;> assumption)
