import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchwartzBruhatSpanIndicators
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FSchwartzBruhatSpanIndicators.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.schwartz_bruhat_span_indicators : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type) [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)), NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ), φ = ∑ a ∈ s, c a • indC N a := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | exact GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators <;> assumption)
