import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsteinSeriesAbsoluteConvergence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEpsteinSeriesAbsoluteConvergence.lean&line=220#L220)
-/
theorem _root_.GlobalTheory.T.epstein_series_absolute_convergence : Ad3.R.G3a := by
  first | exact @GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a | exact GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a | (intros; apply GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a <;> assumption)
