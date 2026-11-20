import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlane
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGamma1CapGamma0LevelActsFreelyUpperHalfPlane.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  first | exact @GlobalTheory.KZ.gam_free | exact GlobalTheory.KZ.gam_free | (intros; apply GlobalTheory.KZ.gam_free <;> assumption)
