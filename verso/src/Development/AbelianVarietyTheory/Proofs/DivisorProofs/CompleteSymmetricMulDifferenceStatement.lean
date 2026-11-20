import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifference
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompleteSymmetricMulDifference.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.complete_symmetric_mul_difference : ∀ k : ℕ, aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) = (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := by
  first | exact @GlobalTheory.LineForm.aeval_hs_mul_sub | exact GlobalTheory.LineForm.aeval_hs_mul_sub | (intros; apply GlobalTheory.LineForm.aeval_hs_mul_sub <;> assumption)
