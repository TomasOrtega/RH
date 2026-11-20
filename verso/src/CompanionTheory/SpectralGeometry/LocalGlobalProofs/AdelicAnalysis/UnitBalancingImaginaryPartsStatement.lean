import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitBalancingImaginaryParts
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FUnitBalancingImaginaryParts.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.unit_balancing_imaginary_parts : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ κ : ℝ, 0 < κ ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) → ∃ u : (𝓞 F)ˣ, ∀ v w, κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units | exact GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units | (intros; apply GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units <;> assumption)
