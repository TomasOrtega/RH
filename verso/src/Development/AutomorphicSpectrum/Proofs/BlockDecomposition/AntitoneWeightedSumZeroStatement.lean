import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneWeightedSumZero

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAntitoneWeightedSumZero.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.antitone_weighted_sum_zero : ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 → (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) → ∀ i, e i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | exact GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | (intros; apply GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg <;> assumption)
