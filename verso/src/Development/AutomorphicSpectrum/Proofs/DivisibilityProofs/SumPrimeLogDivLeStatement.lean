import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumPrimeLogDivLe
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FSumPrimeLogDivLe.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.sum_prime_log_div_le : ∀ x : ℝ, 1 ≤ x → ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + Real.log 4 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four | exact GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four <;> assumption)
