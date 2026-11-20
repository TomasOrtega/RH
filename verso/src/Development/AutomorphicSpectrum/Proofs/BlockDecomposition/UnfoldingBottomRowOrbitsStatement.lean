import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingBottomRowOrbits
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnfoldingBottomRowOrbits.lean&line=299#L299)
-/
theorem _root_.GlobalTheory.T.unfolding_bottom_row_orbits : Ad3.R.G2a := by
  first | exact @GlobalTheory.CompanionTheory.RSCoord.coord_exists | exact GlobalTheory.CompanionTheory.RSCoord.coord_exists | (intros; apply GlobalTheory.CompanionTheory.RSCoord.coord_exists <;> assumption)
