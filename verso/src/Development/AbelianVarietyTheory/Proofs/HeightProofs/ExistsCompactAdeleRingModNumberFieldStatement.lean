import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Mathlib
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.AdeleCocompact.exists_compact_adele | exact GlobalTheory.AdeleCocompact.exists_compact_adele | (intros; apply GlobalTheory.AdeleCocompact.exists_compact_adele <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_compact_adeleRing_mod_numberField : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  first | exact @GlobalTheory.AdeleCocompact.exists_compact_adele | exact GlobalTheory.AdeleCocompact.exists_compact_adele | (intros; apply GlobalTheory.AdeleCocompact.exists_compact_adele <;> assumption)
