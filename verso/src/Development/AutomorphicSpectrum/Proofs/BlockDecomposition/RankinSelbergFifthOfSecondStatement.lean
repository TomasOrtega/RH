import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFifthOfSecond
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergFifthOfSecond.lean&line=438#L438)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_fifth_of_second : Ad3.R.A2 → Ad3.R.A5 := by
  first | exact @GlobalTheory.CompanionTheory.RSPlane.measure_plane_eq_rows | exact GlobalTheory.CompanionTheory.RSPlane.measure_plane_eq_rows | (intros; apply GlobalTheory.CompanionTheory.RSPlane.measure_plane_eq_rows <;> assumption)
