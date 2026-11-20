import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FConvergenceStatementHolds.lean&line=234#L234)
-/
theorem _root_.GlobalTheory.T.convergence_statement_holds : ConvergenceStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds <;> assumption)
