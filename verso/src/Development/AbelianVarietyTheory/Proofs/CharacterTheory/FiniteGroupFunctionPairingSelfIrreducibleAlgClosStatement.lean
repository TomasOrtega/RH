import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FFiniteGroupFunctionPairingSelfIrreducibleAlgClos.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), IsIrrChar L L χ → pair χ χ = 1 := by
  first | exact @GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | exact GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | (intros; apply GlobalTheory.BI.pair_self_of_isIrrChar_algClosed <;> assumption)
