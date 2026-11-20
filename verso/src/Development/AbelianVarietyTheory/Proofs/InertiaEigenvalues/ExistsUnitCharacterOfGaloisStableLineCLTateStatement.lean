import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTate
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Per.exists_unit_character_of_stable_line` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsUnitCharacterOfGaloisStableLineCLTate.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate : ∀ (l : ℕ) [Fact l.Prime] (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) → ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  first | exact @GlobalTheory.Per.exists_unit_character_of_stable_line | exact GlobalTheory.Per.exists_unit_character_of_stable_line | (intros; apply GlobalTheory.Per.exists_unit_character_of_stable_line <;> assumption)
