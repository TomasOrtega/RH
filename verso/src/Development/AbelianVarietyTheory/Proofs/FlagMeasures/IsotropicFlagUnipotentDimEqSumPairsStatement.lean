import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentDimEqSumPairs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsotropicFlagUnipotentDimEqSumPairs.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | exact GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | (intros; apply GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs <;> assumption)
