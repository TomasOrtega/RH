import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockFormCurveClassDegreeSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBlockFormCurveClassDegreeSum.lean&line=191#L191)
-/
theorem _root_.GlobalTheory.T.block_form_curve_class_degree_sum : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), 1 ≤ j → j < N → ∑ τ : ι, formDeg (blkForm j τ * toForm (curveCl ι N j)) = (1 / (j : ℝ) - 1 / ((N : ℝ) - j)) * ∑ τ : ι, formDeg (toForm (pLow j τ 1 * curveCl ι N j) : FormPol ι N) := by
  first | exact @GlobalTheory.FlagCurve.blk_curve_main | exact GlobalTheory.FlagCurve.blk_curve_main | (intros; apply GlobalTheory.FlagCurve.blk_curve_main <;> assumption)
