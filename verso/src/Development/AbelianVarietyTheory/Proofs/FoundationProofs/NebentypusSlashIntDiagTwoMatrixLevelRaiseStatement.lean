import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaise
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNebentypusSlashIntDiagTwoMatrixLevelRaise.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise : ∀ (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg <;> assumption)
