import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddMulLeOfPowLeOfLarge
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VSubArith.add_mul_le_of_pow_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAddMulLeOfPowLeOfLarge.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.add_mul_le_of_pow_le_of_large : ∀ (p L m : ℕ), 2 ≤ p → ∃ M0 : ℕ, ∀ n v : ℕ, M0 ≤ n → p ^ v ≤ n → (v + m) * L ≤ n := by
  first | exact @GlobalTheory.VSubArith.add_mul_le_of_pow_le | exact GlobalTheory.VSubArith.add_mul_le_of_pow_le | (intros; apply GlobalTheory.VSubArith.add_mul_le_of_pow_le <;> assumption)
