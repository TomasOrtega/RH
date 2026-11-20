import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRrEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegralRrEqZero.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.integral_right_derivative_zero_alt : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero | exact GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero <;> assumption)
