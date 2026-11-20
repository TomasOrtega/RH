import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCuspFormIsCuspidalAtAllCuspsSL2.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll <;> assumption)
