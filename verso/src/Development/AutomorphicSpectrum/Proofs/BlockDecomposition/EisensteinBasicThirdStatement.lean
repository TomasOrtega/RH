import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThird
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinBasicThird.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.eisenstein_basic_third : Ad3.R.B0 → Ad3.R.E3 := by
  first | exact @GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt | exact GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt | (intros; apply GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt <;> assumption)
