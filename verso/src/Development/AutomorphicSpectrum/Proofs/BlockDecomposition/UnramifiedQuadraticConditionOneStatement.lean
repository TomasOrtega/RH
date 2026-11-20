import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ResidueInvolution.q1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedQuadraticConditionOne.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_one : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  first | exact @GlobalTheory.CompanionTheory.ResidueInvolution.q1 | exact GlobalTheory.CompanionTheory.ResidueInvolution.q1 | (intros; apply GlobalTheory.CompanionTheory.ResidueInvolution.q1 <;> assumption)
