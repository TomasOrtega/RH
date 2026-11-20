import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformTorusVanishing
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformTorusVanishing.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.newform_torus_vanishing : Ad3.R.C1 → Ad3.R.U0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinTorusVanishing.spherical_whittaker_eq_zero | exact GlobalTheory.CompanionTheory.RankinTorusVanishing.spherical_whittaker_eq_zero | (intros; apply GlobalTheory.CompanionTheory.RankinTorusVanishing.spherical_whittaker_eq_zero <;> assumption)
