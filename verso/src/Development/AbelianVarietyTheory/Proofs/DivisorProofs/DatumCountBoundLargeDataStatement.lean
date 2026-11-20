import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.SumCount GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SumCount.DataCount.dataK` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDatumCountBoundLargeData.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.datumCountBound_largeData : GlobalTheory.SumCount.DataK := by
  first | exact @GlobalTheory.SumCount.DataCount.dataK | exact GlobalTheory.SumCount.DataCount.dataK | (intros; apply GlobalTheory.SumCount.DataCount.dataK <;> assumption)
