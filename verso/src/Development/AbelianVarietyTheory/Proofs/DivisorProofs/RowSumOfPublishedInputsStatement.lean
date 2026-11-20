import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfHyp
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RowClaim.rowSum_of_hypotheses | exact GlobalTheory.RowClaim.rowSum_of_hypotheses | (intros; apply GlobalTheory.RowClaim.rowSum_of_hypotheses <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.row_sum_of_published_inputs : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.SumOKK := by
  first | exact @GlobalTheory.RowClaim.rowSum_of_hypotheses | exact GlobalTheory.RowClaim.rowSum_of_hypotheses | (intros; apply GlobalTheory.RowClaim.rowSum_of_hypotheses <;> assumption)
