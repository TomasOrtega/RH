import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeSubOneNormLe
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.pow_prime_sub_one_norm_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPowPrimeSubOneNormLe.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.norm_pow_prime_sub_one_le_of_norm_sub_one_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  first | exact @GlobalTheory.pow_prime_sub_one_norm_le | exact GlobalTheory.pow_prime_sub_one_norm_le | (intros; apply GlobalTheory.pow_prime_sub_one_norm_le <;> assumption)
