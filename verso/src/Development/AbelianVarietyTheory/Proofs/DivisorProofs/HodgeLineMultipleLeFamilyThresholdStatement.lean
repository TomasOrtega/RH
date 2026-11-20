import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineMultipleLeFamilyThreshold
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HodgeMultNum.hodgeMult_le_TO` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeLineMultipleLeFamilyThreshold.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.hodgeLineMultiple_le_familyThreshold : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤ (Fm.parT x hx ι).TO := by
  first | exact @GlobalTheory.HodgeMultNum.hodgeMult_le_TO | exact GlobalTheory.HodgeMultNum.hodgeMult_le_TO | (intros; apply GlobalTheory.HodgeMultNum.hodgeMult_le_TO <;> assumption)
