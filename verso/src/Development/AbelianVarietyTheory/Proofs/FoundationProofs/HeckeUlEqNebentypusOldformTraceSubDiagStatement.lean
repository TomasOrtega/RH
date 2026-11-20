import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeUlEqNebentypusOldformTraceSubDiag.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → UlF k l B = χ (l : ZMod N) • (trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | exact GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld <;> assumption)
