import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIrrCharAdd
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FExistsIrrCharAdd.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  first | exact @GlobalTheory.BI.exists_irrChar_add | exact GlobalTheory.BI.exists_irrChar_add | (intros; apply GlobalTheory.BI.exists_irrChar_add <;> assumption)
