import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfComp
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.away_range_le_of_dvd'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalizationAwayRangeLeOfDvdOfComp.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.localization_away_range_le_of_dvd_of_comp : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range := by
  first | exact @GlobalTheory.away_range_le_of_dvd' | exact GlobalTheory.away_range_le_of_dvd' | (intros; apply GlobalTheory.away_range_le_of_dvd' <;> assumption)
