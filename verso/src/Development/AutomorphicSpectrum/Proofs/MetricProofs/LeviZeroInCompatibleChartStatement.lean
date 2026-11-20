import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChart
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLeviZeroInCompatibleChart.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.levi_zero_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w, levi (g ∘ (A.chart j).symm) y w = 0) → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart | exact GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart | (intros; apply GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart <;> assumption)
