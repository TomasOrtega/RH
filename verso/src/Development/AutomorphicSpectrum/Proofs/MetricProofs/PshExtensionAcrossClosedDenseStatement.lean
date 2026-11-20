import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDense
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FPshExtensionAcrossClosedDense.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.psh_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | exact GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | (intros; apply GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl <;> assumption)
