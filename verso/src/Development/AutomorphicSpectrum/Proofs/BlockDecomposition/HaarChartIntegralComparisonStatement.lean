import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHaarChartIntegralComparison.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.haar_chart_integral_comparison : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)), IsCompact Q → IsCompact S → (∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | exact GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | (intros; apply GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar <;> assumption)
