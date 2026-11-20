import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIntegralOverLocalizationScaled.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.integral_over_localization_scaled : ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K), (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) → ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | exact GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | (intros; apply GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral <;> assumption)
