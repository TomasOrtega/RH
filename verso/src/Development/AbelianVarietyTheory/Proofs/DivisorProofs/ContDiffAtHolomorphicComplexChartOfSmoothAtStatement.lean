import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.contDiffAt_holoChart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContDiffAtHolomorphicComplexChartOfSmoothAt.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  first | exact @GlobalTheory.GoodTop.contDiffAt_holoChart | exact GlobalTheory.GoodTop.contDiffAt_holoChart | (intros; apply GlobalTheory.GoodTop.contDiffAt_holoChart <;> assumption)
