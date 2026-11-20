import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlmostEt.frob_sum_sub_le'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FValuationFrobeniusSumSubLeNatCastPrime.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) → v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  first | exact @GlobalTheory.AlmostEt.frob_sum_sub_le' | exact GlobalTheory.AlmostEt.frob_sum_sub_le' | (intros; apply GlobalTheory.AlmostEt.frob_sum_sub_le' <;> assumption)
