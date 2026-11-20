import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantComponentsOfGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOpenProjectionDominantComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermComponents
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDominantComponentsOfGerm.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.dominant_components_of_germ : AnalyticGermComponents.Statement → OpenProjectionDominantComponents.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents | exact GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents <;> assumption)
