import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLocalizationAtPrimeFactorsThroughAway
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgHomLocalizationAtPrimeFactorsThroughAway.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.algHom_localizationAtPrime_factors_through_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p) (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift (algebraMap B (Localization.AtPrime p)) g (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  first | exact @GlobalTheory.FactorAway.factor_away | exact GlobalTheory.FactorAway.factor_away | (intros; apply GlobalTheory.FactorAway.factor_away <;> assumption)
