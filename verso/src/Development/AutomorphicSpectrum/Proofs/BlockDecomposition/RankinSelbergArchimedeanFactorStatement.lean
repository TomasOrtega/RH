import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergArchimedeanFactor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RankinSelberg.x1a` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergArchimedeanFactor.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_archimedean_factor : Ad3.R.HalfPlaneAnalyticIdentities := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.x1a | exact GlobalTheory.CompanionTheory.RankinSelberg.x1a | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.x1a <;> assumption)
