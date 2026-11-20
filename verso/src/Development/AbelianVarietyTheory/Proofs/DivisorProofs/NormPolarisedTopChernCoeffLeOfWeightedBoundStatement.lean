import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPolarisedTopChernCoeffLeOfWeightedBound
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormPolarisedTopChernCoeffLeOfWeightedBound.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.norm_polarisedTopChernCoeff_le_of_weighted_bound : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  first | exact @GlobalTheory.GoodTop.norm_mixTop_le_of_weighted | exact GlobalTheory.GoodTop.norm_mixTop_le_of_weighted | (intros; apply GlobalTheory.GoodTop.norm_mixTop_le_of_weighted <;> assumption)
