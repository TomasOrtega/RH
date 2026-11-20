import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOn
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.hasInt_congr_on` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasTopFormChartIntegralCongrOn.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ}, (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  first | exact @GlobalTheory.GoodTop.hasInt_congr_on | exact GlobalTheory.GoodTop.hasInt_congr_on | (intros; apply GlobalTheory.GoodTop.hasInt_congr_on <;> assumption)
