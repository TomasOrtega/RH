import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FQBinomialFinite.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  first | exact @GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | exact GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | (intros; apply GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite <;> assumption)
