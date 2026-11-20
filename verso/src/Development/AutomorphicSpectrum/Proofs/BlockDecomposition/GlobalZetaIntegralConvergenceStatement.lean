import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralConvergence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RSZeta.functional_equation` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGlobalZetaIntegralConvergence.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.global_zeta_integral_convergence : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4 := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.functional_equation | exact GlobalTheory.CompanionTheory.RSZeta.functional_equation | (intros; apply GlobalTheory.CompanionTheory.RSZeta.functional_equation <;> assumption)
