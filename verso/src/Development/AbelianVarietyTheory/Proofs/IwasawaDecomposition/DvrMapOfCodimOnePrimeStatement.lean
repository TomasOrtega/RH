import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrMapOfCodimOnePrime
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.trait_unramified_of_prime_below` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDvrMapOfCodimOnePrime.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.dvr_map_of_codim_one_prime : ∀ {A R W : Type} [CommRing A] [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : A →+* R) (Q : Ideal R) [Q.IsPrime], IsDiscreteValuationRing (Localization.AtPrime Q) → (Q.comap φ).map ((algebraMap R (Localization.AtPrime Q)).comp φ) = maximalIdeal (Localization.AtPrime Q) → ∀ (ϖ : W), Irreducible ϖ → maximalIdeal W = Ideal.span {ϖ} → ∀ g : R →+* W, (∀ r, r ∉ Q → IsUnit (g r)) → (∃ π ∈ Q, Associated (g π) ϖ) → (Q.comap φ).map (g.comp φ) = maximalIdeal W ∧ (maximalIdeal W).comap g = Q := by
  first | exact @GlobalTheory.trait_unramified_of_prime_below | exact GlobalTheory.trait_unramified_of_prime_below | (intros; apply GlobalTheory.trait_unramified_of_prime_below <;> assumption)
