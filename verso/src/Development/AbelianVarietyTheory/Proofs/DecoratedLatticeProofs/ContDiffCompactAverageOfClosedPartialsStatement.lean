import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffCompactAverageOfClosedPartials
import Mathlib
open MeasureTheory
open scoped ContDiff

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AvgSmooth.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FContDiffCompactAverageOfClosedPartials.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.contDiff_compactAverage_of_closed_partials : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  first | exact @GlobalTheory.AvgSmooth.main | exact GlobalTheory.AvgSmooth.main | (intros; apply GlobalTheory.AvgSmooth.main <;> assumption)
