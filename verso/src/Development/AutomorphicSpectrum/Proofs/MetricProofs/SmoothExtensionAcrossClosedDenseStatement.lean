import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDense
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SmoothGlue.glue` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSmoothExtensionAcrossClosedDense.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.smooth_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  first | exact @GlobalTheory.CompanionTheory.SmoothGlue.glue | exact GlobalTheory.CompanionTheory.SmoothGlue.glue | (intros; apply GlobalTheory.CompanionTheory.SmoothGlue.glue <;> assumption)
