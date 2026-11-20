import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSignedConvergenceStatementHolds.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.signed_convergence_statement_holds : ConvergenceSignedStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned | exact GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned <;> assumption)
