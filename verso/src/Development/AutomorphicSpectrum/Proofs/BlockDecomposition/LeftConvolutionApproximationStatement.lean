import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftConvolutionApproximation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeftConvolutionApproximation.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.left_convolution_approximation : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → (∀ y, 0 ≤ φ y) → (∫ y : G n, φ y.val ∂μ = 1) → ∀ (x : Lp V 2 μ) (ε : ℝ), (∀ y : G n, φ y.val ≠ 0 → ‖lT μ V y x - x‖ ≤ ε) → ‖lConv μ V φ x - x‖ ≤ ε := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le | exact GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le | (intros; apply GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le <;> assumption)
