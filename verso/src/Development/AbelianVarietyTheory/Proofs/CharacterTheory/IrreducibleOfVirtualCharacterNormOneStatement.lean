import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BI.irr_of_norm_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FIrreducibleOfVirtualCharacterNormOne.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.irreducible_of_virtualCharacter_norm_one : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  first | exact @GlobalTheory.BI.irr_of_norm_one | exact GlobalTheory.BI.irr_of_norm_one | (intros; apply GlobalTheory.BI.irr_of_norm_one <;> assumption)
