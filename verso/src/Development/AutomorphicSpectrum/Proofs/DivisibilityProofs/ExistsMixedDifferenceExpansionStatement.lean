import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsMixedDifferenceExpansion
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FExistsMixedDifferenceExpansion.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.exists_mixed_difference_expansion : ∀ (σ : Type) [Fintype σ] (n : ℕ) (F : MvPolynomial σ ℝ), F.IsHomogeneous n → ∃ Gs, IsMixExpansion (n - 1) (mixDiff F) Gs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | exact GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff <;> assumption)
