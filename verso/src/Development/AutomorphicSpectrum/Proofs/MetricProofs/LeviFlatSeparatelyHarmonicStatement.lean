import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonic
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLeviFlatSeparatelyHarmonic.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.levi_flat_separately_harmonic : ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O → (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i, InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | exact GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero <;> assumption)
