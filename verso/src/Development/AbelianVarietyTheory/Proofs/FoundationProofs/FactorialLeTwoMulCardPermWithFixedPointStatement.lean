import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FactorialLeTwoMulCardPermWithFixedPoint
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFactorialLeTwoMulCardPermWithFixedPoint.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint : ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α → (Fintype.card α).factorial ≤ 2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  first | exact @GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | exact GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | (intros; apply GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed <;> assumption)
