import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfRecurrenceGrowth
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FNormLeOfRecurrenceGrowth.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.norm_le_of_recurrence_growth' : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  first | exact @GlobalTheory.norm_le_of_recurrence_growth | exact GlobalTheory.norm_le_of_recurrence_growth | (intros; apply GlobalTheory.norm_le_of_recurrence_growth <;> assumption)
