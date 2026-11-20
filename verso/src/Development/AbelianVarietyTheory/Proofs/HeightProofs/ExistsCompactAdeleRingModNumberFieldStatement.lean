import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Mathlib
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdeleCocompact.exists_compact_adele` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FExistsCompactAdeleRingModNumberField.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.exists_compact_adeleRing_mod_numberField : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  first | exact @GlobalTheory.AdeleCocompact.exists_compact_adele | exact GlobalTheory.AdeleCocompact.exists_compact_adele | (intros; apply GlobalTheory.AdeleCocompact.exists_compact_adele <;> assumption)
