import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianIntegrableFiniteDim
universe u
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGaussianIntegrableFiniteDim.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.gaussian_integrable_finite_dim : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.gaussInt | exact GlobalTheory.CompanionTheory.EisTube.gaussInt | (intros; apply GlobalTheory.CompanionTheory.EisTube.gaussInt <;> assumption)
