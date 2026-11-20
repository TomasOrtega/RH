import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulCoeffMem
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardMulCoeffMem.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent : ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  first | exact @GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | exact GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | (intros; apply GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem <;> assumption)
