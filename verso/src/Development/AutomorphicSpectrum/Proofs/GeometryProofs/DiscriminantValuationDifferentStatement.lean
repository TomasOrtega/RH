import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantValuationDifferent
import Mathlib
open NumberField IsDedekindDomain UniqueFactorizationMonoid
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FDiscriminantValuationDifferent.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.discriminant_valuation_different : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)), P.IsPrime → (p : 𝓞 E) ∈ P → ((padicValInt p (discr E) : ℕ)) * (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P = (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | exact GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | (intros; apply GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq <;> assumption)
