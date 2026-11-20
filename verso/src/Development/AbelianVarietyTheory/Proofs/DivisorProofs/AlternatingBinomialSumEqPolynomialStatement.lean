import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingBinomialSumEqPolynomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlternatingBinomialSumEqPolynomial.lean&line=186#L186)
-/
theorem _root_.GlobalTheory.T.alternating_binomial_sum_eq_polynomial : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j) = pm m := by
  first | exact @GlobalTheory.LineForm.sum_choose_hs_eq_pm | exact GlobalTheory.LineForm.sum_choose_hs_eq_pm | (intros; apply GlobalTheory.LineForm.sum_choose_hs_eq_pm <;> assumption)
