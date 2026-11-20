import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsGoodStatement
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FGenericPointsGoodStatement.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.generic_points_good_statement : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.blockProjection_genericPoints_good | exact GlobalTheory.CompanionTheory.Ggeo.blockProjection_genericPoints_good | (intros; apply GlobalTheory.CompanionTheory.Ggeo.blockProjection_genericPoints_good <;> assumption)
