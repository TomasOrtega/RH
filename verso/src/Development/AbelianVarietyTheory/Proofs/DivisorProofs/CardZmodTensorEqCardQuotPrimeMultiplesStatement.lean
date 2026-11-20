import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardZmodTensorEqCardQuotPrimeMultiples
import Mathlib
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardZmodTensorEqCardQuotPrimeMultiples.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ), Nat.card (TensorProduct ℤ (ZMod p) M) = Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  first | exact @GlobalTheory.card_zmod_tensor_eq_card_quot' | exact GlobalTheory.card_zmod_tensor_eq_card_quot' | (intros; apply GlobalTheory.card_zmod_tensor_eq_card_quot' <;> assumption)
