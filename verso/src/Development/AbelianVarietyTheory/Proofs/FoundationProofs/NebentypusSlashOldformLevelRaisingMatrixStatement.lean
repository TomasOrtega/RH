import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashOldformLevelRaisingMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNebentypusSlashOldformLevelRaisingMatrix.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld <;> assumption)
