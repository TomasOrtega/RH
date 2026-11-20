import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviNonnegInChartOfPsh
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLeviNonnegInChartOfPsh.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.levi_nonneg_in_chart_of_psh : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B → IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) → (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  first | exact @GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase | exact GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase | (intros; apply GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase <;> assumption)
