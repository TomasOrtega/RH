import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLocalizationAtPrimeIsDiscreteValuationRingOfHeig.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | exact GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | (intros; apply GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one <;> assumption)
