import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSegreChartIntegralHolds.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.segre_chart_integral_holds : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | exact GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral <;> assumption)
