import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormLambdaEqTwoSumCrossing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagCurve.toForm_lamA_eq_two_mul_cross` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormLambdaEqTwoSumCrossing.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.form_lambda_eq_two_sum_crossing : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), (toForm (lamA ι N j) : FormPol ι N) = 2 * ∑ s ∈ crSet ι N j, X s := by
  first | exact @GlobalTheory.FlagCurve.toForm_lamA_eq_two_mul_cross | exact GlobalTheory.FlagCurve.toForm_lamA_eq_two_mul_cross | (intros; apply GlobalTheory.FlagCurve.toForm_lamA_eq_two_mul_cross <;> assumption)
