import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoercive
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FFiniteDimensionalOfCompactCoercive.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c → (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | exact GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | (intros; apply GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive <;> assumption)
