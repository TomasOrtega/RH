import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqPrimePowMulNotDvdCompletedLaurent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsEqPrimePowMulNotDvdCompletedLaurent.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_eq_prime_pow_mul_not_dvd_O0 : ∀ (p : ℕ) [Fact p.Prime], ∀ x : O0 p, x ≠ 0 → ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := by
  first | exact @GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent | exact GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent | (intros; apply GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent <;> assumption)
