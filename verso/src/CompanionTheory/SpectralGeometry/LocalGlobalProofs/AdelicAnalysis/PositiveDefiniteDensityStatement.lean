import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveDefiniteDensity
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.Core.Density.exists_density` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FPositiveDefiniteDensity.lean&line=252#L252)
-/
theorem _root_.GlobalTheory.T.positive_definite_density : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ (m : Measure V), IsFiniteMeasure m → Integrable (fun y => ∫ x, χ x y ∂m) μ → ∃ D : V → ℝ, Continuous D ∧ (∀ x, 0 ≤ D x) ∧ (∀ x, (D x : ℂ) = ∫ y, (∫ z, χ z y ∂m) * χ (-x) y ∂μ) ∧ ∀ U : Set V, MeasurableSet U → m U = ∫⁻ x in U, ENNReal.ofReal (D x) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Density.exists_density | exact GlobalTheory.CompanionTheory.SW.Core.Density.exists_density | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Density.exists_density <;> assumption)
