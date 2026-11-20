import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHolds
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
Apply `GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCurveBranchLengthHolds.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.curve_branch_length_holds : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | exact GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | (intros; apply GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength <;> assumption)
