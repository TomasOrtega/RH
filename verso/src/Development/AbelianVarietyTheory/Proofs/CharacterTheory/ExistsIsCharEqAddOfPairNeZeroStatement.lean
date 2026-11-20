import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIsCharEqAddOfPairNeZero
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FExistsIsCharEqAddOfPairNeZero.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_isChar_eq_add_of_pair_ne_zero' : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (φ a : G → L), IsIrrChar K L φ → IsChar K L a → pair a φ ≠ 0 → ∃ c : G → L, IsChar K L c ∧ a = φ + c := by
  first | exact @GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero | exact GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero | (intros; apply GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero <;> assumption)
