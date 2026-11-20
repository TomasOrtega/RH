import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFour
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedQuadraticConditionFour.lean&line=234#L234)
-/
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_four : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  first | exact @GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | exact GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | (intros; apply GlobalTheory.CompanionTheory.DiscriminantUnit.q4 <;> assumption)
