import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTimesGaussianBounded
universe u
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPolynomialTimesGaussianBounded.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.polynomial_times_gaussian_bounded : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | exact GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | (intros; apply GlobalTheory.CompanionTheory.EisTube.polyGaussBdd <;> assumption)
