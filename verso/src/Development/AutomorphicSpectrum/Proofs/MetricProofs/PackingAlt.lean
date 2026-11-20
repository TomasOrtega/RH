import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.WeilBound.CoreStatements.RationalSupMetrics.PullRatiosAlgebraic

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

/- English proof (translation)
The claim follows from `MultiProjectiveCoordinates.packing_statement`.
-/
theorem packing : PackingStatement := MultiProjectiveCoordinates.packing_statement

end GlobalTheory.CompanionTheory.Ar.Small
