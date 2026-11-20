import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierInversionSchwartzBruhat
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.FouSB.fou_sb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FFourierInversionSchwartzBruhat.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.fourier_inversion_schwartz_bruhat : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FouSB.fou_sb | exact GlobalTheory.CompanionTheory.SW.FouSB.fou_sb | (intros; apply GlobalTheory.CompanionTheory.SW.FouSB.fou_sb <;> assumption)
