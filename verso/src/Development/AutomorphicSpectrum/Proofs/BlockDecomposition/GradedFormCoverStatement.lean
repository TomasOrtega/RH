import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCover
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GrForm.AffCover.stCover` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGradedFormCover.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.graded_form_cover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | exact GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | (intros; apply GlobalTheory.CompanionTheory.GrForm.AffCover.stCover <;> assumption)
