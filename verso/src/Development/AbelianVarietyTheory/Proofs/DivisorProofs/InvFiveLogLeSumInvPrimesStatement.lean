import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes
import Mathlib
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInvFiveLogLeSumInvPrimes.lean&line=303#L303)
-/
theorem _root_.GlobalTheory.T.inv_five_log_le_sum_inv_primes_half_interval : ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤ ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N), (1 : ℝ) / p := by
  first | exact @GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes | exact GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes | (intros; apply GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes <;> assumption)
