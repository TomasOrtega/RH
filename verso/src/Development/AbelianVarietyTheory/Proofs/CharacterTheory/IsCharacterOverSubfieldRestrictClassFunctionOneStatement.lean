import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FIsCharacterOverSubfieldRestrictClassFunctionOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (χ : G → L), IsChar K L χ → (∀ (H : Type) [Group H] (f : H →* G), IsChar K L (fun h => χ (f h))) ∧ (∀ g x : G, χ (x⁻¹ * g * x) = χ g) ∧ ∃ n : ℕ, χ 1 = (n : L) ∧ (n = 0 → χ = 0) := by
  first | exact @GlobalTheory.isChar_restrict_conj_one | exact GlobalTheory.isChar_restrict_conj_one | (intros; apply GlobalTheory.isChar_restrict_conj_one <;> assumption)
