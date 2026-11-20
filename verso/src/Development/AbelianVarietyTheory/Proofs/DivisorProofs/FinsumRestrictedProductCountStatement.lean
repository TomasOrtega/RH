import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRestrictedProductCount
import Mathlib
open Filter
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinsumRestrictedProductCount.lean&line=174#L174)
-/
theorem _root_.GlobalTheory.T.finsum_restricted_product_count : ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) → (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) → (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) → (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) → Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) → (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k = (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  first | exact @GlobalTheory.finsum_finprod_mul_two_pow_eq | exact GlobalTheory.finsum_finprod_mul_two_pow_eq | (intros; apply GlobalTheory.finsum_finprod_mul_two_pow_eq <;> assumption)
