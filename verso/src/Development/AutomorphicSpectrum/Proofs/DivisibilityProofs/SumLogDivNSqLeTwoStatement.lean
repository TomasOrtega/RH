import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivNSqLeTwo
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Small.log_tail` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FSumLogDivNSqLeTwo.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.sum_log_div_n_sq_le_two : ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) → ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.log_tail | exact GlobalTheory.CompanionTheory.Ar.Small.log_tail | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.log_tail <;> assumption)
