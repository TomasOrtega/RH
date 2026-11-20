import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvr
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAssociatedPrimeLocalizationDvr.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.associated_prime_localization_dvr : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 → (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) → ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  first | exact @GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | exact GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | (intros; apply GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient <;> assumption)
