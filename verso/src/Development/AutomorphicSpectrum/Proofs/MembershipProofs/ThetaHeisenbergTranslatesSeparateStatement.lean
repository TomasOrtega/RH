import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparate
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMembershipProofs%2FThetaHeisenbergTranslatesSeparate.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.rational_units_haar_character_one : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (a : Fˣ), distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal | exact GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal | (intros; apply GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal <;> assumption)
