import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowCountAllBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LowCount.lowC_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLowCountAllBounds.lean&line=191#L191)
-/
theorem _root_.GlobalTheory.T.low_count_all_bounds : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality := by
  first | exact @GlobalTheory.LowCount.lowC_all | exact GlobalTheory.LowCount.lowC_all | (intros; apply GlobalTheory.LowCount.lowC_all <;> assumption)
