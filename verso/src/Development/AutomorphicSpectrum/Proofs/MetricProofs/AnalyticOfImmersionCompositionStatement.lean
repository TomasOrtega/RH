import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionComposition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FAnalyticOfImmersionComposition.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.analytic_of_immersion_composition : ∀ {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V) (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ), AnalyticAt ℂ ψ (F y₀) → (fderiv ℂ ψ (F y₀)).ker = ⊥ → AnalyticAt ℂ H y₀ → ContinuousAt F y₀ → (∀ᶠ y in nhds y₀, ψ (F y) = H y) → AnalyticAt ℂ F y₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | exact GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | (intros; apply GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion <;> assumption)
