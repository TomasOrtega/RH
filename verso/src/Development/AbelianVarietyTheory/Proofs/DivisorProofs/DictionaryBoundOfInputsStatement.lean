import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryBoundOfInputs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SumSize.dictK_of_normSum` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDictionaryBoundOfInputs.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.dictionary_bound_of_inputs : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK := by
  first | exact @GlobalTheory.SumSize.dictK_of_normSum | exact GlobalTheory.SumSize.dictK_of_normSum | (intros; apply GlobalTheory.SumSize.dictK_of_normSum <;> assumption)
