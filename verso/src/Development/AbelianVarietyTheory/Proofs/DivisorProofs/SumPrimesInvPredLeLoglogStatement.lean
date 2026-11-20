import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPrimesInvPredLeLoglog
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrimeRecipSum.sum_inv_pred_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumPrimesInvPredLeLoglog.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.sum_primes_inv_pred_le_loglog : ∀ y : ℕ, 3 ≤ y → ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 7 * Real.log (Real.log y) + 6 := by
  first | exact @GlobalTheory.PrimeRecipSum.sum_inv_pred_le | exact GlobalTheory.PrimeRecipSum.sum_inv_pred_le | (intros; apply GlobalTheory.PrimeRecipSum.sum_inv_pred_le <;> assumption)
