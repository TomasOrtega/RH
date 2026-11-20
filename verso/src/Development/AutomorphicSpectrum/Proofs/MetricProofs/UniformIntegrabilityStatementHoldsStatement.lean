import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FUniformIntegrabilityStatementHolds.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.uniform_integrability_statement_holds : UnifIntStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds <;> assumption)
