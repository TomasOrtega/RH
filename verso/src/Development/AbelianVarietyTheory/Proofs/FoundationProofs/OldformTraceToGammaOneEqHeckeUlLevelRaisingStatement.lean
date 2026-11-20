import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformTraceToGammaOneEqHeckeUlLevelRaising
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FOldformTraceToGammaOneEqHeckeUlLevelRaising.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ), 0 < l → trOld k N l a b h G = G + ((l : ℂ) ^ (2 - k)) • UlF k l (G ∣[k] toGL (wOld N l a b)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.trOld_eq | exact GlobalTheory.HeckeFamilyMatrices.trOld_eq | (intros; apply GlobalTheory.HeckeFamilyMatrices.trOld_eq <;> assumption)
