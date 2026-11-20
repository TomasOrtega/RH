import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentExpInjectiveCommuting
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNilpotentExpInjectiveCommuting.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.nilpotent_exp_injective_commuting : ∀ (A : Type) [Ring A] [Algebra ℚ A] (a b : A), Commute a b → IsNilpotent a → IsNilpotent b → IsNilpotent.exp a = IsNilpotent.exp b → a = b := by
  first | exact @GlobalTheory.exp_injective_of_commute | exact GlobalTheory.exp_injective_of_commute | (intros; apply GlobalTheory.exp_injective_of_commute <;> assumption)
