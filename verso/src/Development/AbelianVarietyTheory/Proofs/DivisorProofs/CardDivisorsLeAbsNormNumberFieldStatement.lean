import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDivisorsLeAbsNormNumberField
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardDivisorsLeAbsNormNumberField.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.card_divisors_le_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  first | exact @GlobalTheory.card_le_absNorm_of_forall_le | exact GlobalTheory.card_le_absNorm_of_forall_le | (intros; apply GlobalTheory.card_le_absNorm_of_forall_le <;> assumption)
