import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGiven
import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FBaseMetricExistsOfGiven.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.base_metric_exists_of_given : Given → PB.BaseMetricExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given <;> assumption)
