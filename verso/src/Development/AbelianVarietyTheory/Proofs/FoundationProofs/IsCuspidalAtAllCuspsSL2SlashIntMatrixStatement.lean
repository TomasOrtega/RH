import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsCuspidalAtAllCuspsSL2SlashIntMatrix.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det → CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | exact GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL <;> assumption)
