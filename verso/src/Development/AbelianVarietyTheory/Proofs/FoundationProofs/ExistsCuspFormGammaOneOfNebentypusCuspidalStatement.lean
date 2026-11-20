import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGammaOneOfNebentypusCuspidal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsCuspFormGammaOneOfNebentypusCuspidal.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv <;> assumption)
