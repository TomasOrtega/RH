import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLe
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FProdPrimesBelowInvOneSubOneDivRpowLe.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le : ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  first | exact @GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | exact GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | (intros; apply GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le <;> assumption)
