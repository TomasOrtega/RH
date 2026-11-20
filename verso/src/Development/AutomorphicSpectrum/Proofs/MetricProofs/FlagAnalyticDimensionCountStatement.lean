import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCount
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FFlagAnalyticDimensionCount.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.flag_analytic_dimension_count : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim <;> assumption)
