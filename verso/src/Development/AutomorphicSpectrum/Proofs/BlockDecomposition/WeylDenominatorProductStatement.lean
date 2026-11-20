import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProduct
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeylDenominatorProduct.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.weyl_denominator_product : ∀ {n : ℕ} (z : Fin n → ℂ), (∀ a, z a ≠ 0) → (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | exact GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow <;> assumption)
