import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentPolynomialInAction
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FEigenComponentPolynomialInAction.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.eigen_component_polynomial_in_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ), ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum <;> assumption)
