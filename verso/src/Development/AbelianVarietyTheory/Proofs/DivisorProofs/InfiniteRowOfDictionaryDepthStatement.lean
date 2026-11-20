import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteRowOfDictionaryDepth
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInfiniteRowOfDictionaryDepth.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.infinite_row_of_dictionary_depth : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfRowK := by
  first | exact @GlobalTheory.SumSize.OppConj.infRowK_main | exact GlobalTheory.SumSize.OppConj.infRowK_main | (intros; apply GlobalTheory.SumSize.OppConj.infRowK_main <;> assumption)
