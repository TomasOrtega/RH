import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChart
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSmoothInCompatibleChart.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.smooth_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  first | exact @GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | exact GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | (intros; apply GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm <;> assumption)
