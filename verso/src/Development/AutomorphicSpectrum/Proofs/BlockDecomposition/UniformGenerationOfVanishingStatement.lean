import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformGenerationOfVanishing.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.uniform_generation_of_vanishing : GradedNoeth → UniformVanishing → UniformGen := by
  first | exact @GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | exact GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | (intros; apply GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth <;> assumption)
