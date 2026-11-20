import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FPullbackStatementHolds.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.pullback_statement_holds : PullbackStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | exact GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement <;> assumption)
