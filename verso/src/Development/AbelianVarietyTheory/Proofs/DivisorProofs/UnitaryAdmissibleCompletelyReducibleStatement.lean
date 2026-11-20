import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdmissibleCompletelyReducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
open GlobalTheory.ThK.SplitInv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.SplitInv.compRed_of_unitary` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryAdmissibleCompletelyReducible.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.unitary_admissible_completely_reducible : ∀ (H : Type) [Group H] (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)) (𝒦 : Set (Subgroup H)), RStable G₀ S → SmAdm G₀ S 𝒦 → Unitary G₀ S → CompRed G₀ S := by
  first | exact @GlobalTheory.ThK.SplitInv.compRed_of_unitary | exact GlobalTheory.ThK.SplitInv.compRed_of_unitary | (intros; apply GlobalTheory.ThK.SplitInv.compRed_of_unitary <;> assumption)
