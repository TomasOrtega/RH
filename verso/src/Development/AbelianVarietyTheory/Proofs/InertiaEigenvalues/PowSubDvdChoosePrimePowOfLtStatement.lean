import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSubDvdChoosePrimePowOfLt
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPowSubDvdChoosePrimePowOfLt.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt : ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  first | exact @GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | exact GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | (intros; apply GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt <;> assumption)
