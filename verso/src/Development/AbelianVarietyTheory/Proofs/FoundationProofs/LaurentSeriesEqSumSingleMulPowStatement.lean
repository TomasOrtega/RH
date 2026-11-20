import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPow
import Mathlib
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FLaurentSeriesEqSumSingleMulPow.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime : ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  first | exact @GlobalTheory.laurentSeries_eq_sum_single_mul_pow | exact GlobalTheory.laurentSeries_eq_sum_single_mul_pow | (intros; apply GlobalTheory.laurentSeries_eq_sum_single_mul_pow <;> assumption)
