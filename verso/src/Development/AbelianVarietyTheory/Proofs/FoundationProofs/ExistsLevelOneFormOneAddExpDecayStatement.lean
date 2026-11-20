import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecay
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.levelOne_form_one_add_expDecay` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLevelOneFormOneAddExpDecay.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_levelOne_form_one_add_expDecay : ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧ (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.levelOne_form_one_add_expDecay | exact GlobalTheory.levelOne_form_one_add_expDecay | (intros; apply GlobalTheory.levelOne_form_one_add_expDecay <;> assumption)
