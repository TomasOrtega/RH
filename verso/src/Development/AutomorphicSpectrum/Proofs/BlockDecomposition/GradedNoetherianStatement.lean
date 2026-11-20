import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedNoetherian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGradedNoetherian.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.graded_noetherian : GradedNoeth := by
  first | exact @GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth | exact GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth | (intros; apply GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth <;> assumption)
