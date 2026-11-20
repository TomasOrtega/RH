import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformMultiplicityOne
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RankinTestVector.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewformMultiplicityOne.lean&line=638#L638)
-/
theorem _root_.GlobalTheory.T.newform_multiplicity_one : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinTestVector.main | exact GlobalTheory.CompanionTheory.RankinTestVector.main | (intros; apply GlobalTheory.CompanionTheory.RankinTestVector.main <;> assumption)
