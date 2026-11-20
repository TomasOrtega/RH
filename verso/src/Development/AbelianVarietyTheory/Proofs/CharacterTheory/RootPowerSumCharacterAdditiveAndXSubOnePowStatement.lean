import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FRootPowerSumCharacterAdditiveAndXSubOnePow.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow : ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ), IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  first | exact @GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one | exact GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one | (intros; apply GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one <;> assumption)
