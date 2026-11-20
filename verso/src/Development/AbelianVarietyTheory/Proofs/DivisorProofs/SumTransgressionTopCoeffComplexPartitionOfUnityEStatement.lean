import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityE
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumTransgressionTopCoeffComplexPartitionOfUnityE.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι] (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) → (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  first | exact @GlobalTheory.GoodTop.corrC_sum_eq_zero | exact GlobalTheory.GoodTop.corrC_sum_eq_zero | (intros; apply GlobalTheory.GoodTop.corrC_sum_eq_zero <;> assumption)
