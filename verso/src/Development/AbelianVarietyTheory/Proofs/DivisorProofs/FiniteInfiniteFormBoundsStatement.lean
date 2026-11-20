import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBounds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormVal.form_fin_inf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteInfiniteFormBounds.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.finite_infinite_form_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinFormK ∧ InfFormK := by
  first | exact @GlobalTheory.FormVal.form_fin_inf | exact GlobalTheory.FormVal.form_fin_inf | (intros; apply GlobalTheory.FormVal.form_fin_inf <;> assumption)
