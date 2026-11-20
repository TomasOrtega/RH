import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterFinsumConjSubgroupFunctionExtendByZer
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FIsCharacterFinsumConjSubgroupFunctionExtendByZer.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  first | exact @GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | exact GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | (intros; apply GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar <;> assumption)
