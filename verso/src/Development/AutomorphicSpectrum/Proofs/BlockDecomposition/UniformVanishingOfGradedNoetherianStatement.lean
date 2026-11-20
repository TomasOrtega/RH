import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishingOfGradedNoetherian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.UV.uniformVanishing` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformVanishingOfGradedNoetherian.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.uniform_vanishing_of_graded_noetherian : GradedNoeth → UniformVanishing := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | exact GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | (intros; apply GlobalTheory.CompanionTheory.GE.UV.uniformVanishing <;> assumption)
