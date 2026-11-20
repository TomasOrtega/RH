import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformMultiplicityOneUnramified
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SphericalVector.m0` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformMultiplicityOneUnramified.lean&line=379#L379)
-/
theorem _root_.GlobalTheory.T.newform_multiplicity_one_unramified : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M0 := by
  first | exact @GlobalTheory.CompanionTheory.SphericalVector.m0 | exact GlobalTheory.CompanionTheory.SphericalVector.m0 | (intros; apply GlobalTheory.CompanionTheory.SphericalVector.m0 <;> assumption)
