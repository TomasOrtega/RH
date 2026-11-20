import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GrForm.stCocycle` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGradedFormCocycle.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.graded_form_cocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stCocycle | exact GlobalTheory.CompanionTheory.GrForm.stCocycle | (intros; apply GlobalTheory.CompanionTheory.GrForm.stCocycle <;> assumption)
