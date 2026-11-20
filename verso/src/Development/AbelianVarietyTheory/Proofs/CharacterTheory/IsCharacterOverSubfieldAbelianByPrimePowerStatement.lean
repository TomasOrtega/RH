import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BI.isChar_of_abByP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FIsCharacterOverSubfieldAbelianByPrimePower.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_abByP | exact GlobalTheory.BI.isChar_of_abByP | (intros; apply GlobalTheory.BI.isChar_of_abByP <;> assumption)
