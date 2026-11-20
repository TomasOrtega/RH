import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwo
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.prod_primesBelow_zeta_two_add_le_two` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FProdPrimesBelowZetaTwoAddLeTwo.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le : ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  first | exact @GlobalTheory.prod_primesBelow_zeta_two_add_le_two | exact GlobalTheory.prod_primesBelow_zeta_two_add_le_two | (intros; apply GlobalTheory.prod_primesBelow_zeta_two_add_le_two <;> assumption)
