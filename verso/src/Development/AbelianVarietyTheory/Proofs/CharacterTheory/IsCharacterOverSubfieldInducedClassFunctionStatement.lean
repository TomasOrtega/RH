import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FIsCharacterOverSubfieldInducedClassFunction.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (ind H ψ) := by
  first | exact @GlobalTheory.BI.isChar_ind | exact GlobalTheory.BI.isChar_ind | (intros; apply GlobalTheory.BI.isChar_ind <;> assumption)
