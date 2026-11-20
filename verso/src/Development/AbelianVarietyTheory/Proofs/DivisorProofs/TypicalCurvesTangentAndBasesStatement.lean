import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBases
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTypicalCurvesTangentAndBases.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.typicalCurveEigenspace_and_basisExists : TypicalCurveEigenspace ∧ TypicalCurveBasisExists := by
  first | exact @GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | exact GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | (intros; apply GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases <;> assumption)
