import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FFiniteGroupFunctionPairingEqZeroOfDistinctIrredu.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ), IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  first | exact @GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | (intros; apply GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne <;> assumption)
