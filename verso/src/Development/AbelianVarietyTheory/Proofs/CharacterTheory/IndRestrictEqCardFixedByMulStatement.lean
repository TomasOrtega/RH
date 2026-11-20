import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndRestrictEqCardFixedByMul
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FIndRestrictEqCardFixedByMul.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  first | exact @GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul | exact GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul | (intros; apply GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul <;> assumption)
