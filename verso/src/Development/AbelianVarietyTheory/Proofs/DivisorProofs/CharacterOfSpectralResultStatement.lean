import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterOfSpectralResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.charSt_of_specSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCharacterOfSpectralResult.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.character_of_spectral_result : SpecSt → CharSt := by
  first | exact @GlobalTheory.HalfGeo.charSt_of_specSt | exact GlobalTheory.HalfGeo.charSt_of_specSt | (intros; apply GlobalTheory.HalfGeo.charSt_of_specSt <;> assumption)
