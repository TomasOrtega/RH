import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingAlt
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FPackingAlt.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.packing' : PackingStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.packing | exact GlobalTheory.CompanionTheory.Ar.Small.packing | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.packing <;> assumption)
