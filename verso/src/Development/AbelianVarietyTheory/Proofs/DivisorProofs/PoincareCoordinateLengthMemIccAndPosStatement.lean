import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPos
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPoincareCoordinateLengthMemIccAndPos.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  first | exact @GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos | exact GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos | (intros; apply GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos <;> assumption)
