import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHolds
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegBallMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSliceBranchesHolds.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.slice_branches_holds : GroundTheory.Heights₂.Heights.SliceBranches.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | exact GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | (intros; apply GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches <;> assumption)
