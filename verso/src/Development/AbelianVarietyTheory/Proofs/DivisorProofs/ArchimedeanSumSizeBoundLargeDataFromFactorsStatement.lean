import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactors
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchimedeanSumSizeBoundLargeDataFromFactors.lean&line=900#L900)
-/
theorem _root_.GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors : SumOKK → DepthK → InfScalK → InfTensK → InfCountK → InfClassK → InfTopK → InfRowK → InfPairK → InfPsiK → InfFormK → InfK := by
  first | exact @GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | exact GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | (intros; apply GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors <;> assumption)
