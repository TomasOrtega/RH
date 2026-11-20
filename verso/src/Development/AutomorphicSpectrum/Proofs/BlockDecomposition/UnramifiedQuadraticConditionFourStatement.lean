import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFour
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | exact GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | (intros; apply GlobalTheory.CompanionTheory.DiscriminantUnit.q4 <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_four : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  first | exact @GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | exact GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | (intros; apply GlobalTheory.CompanionTheory.DiscriminantUnit.q4 <;> assumption)
