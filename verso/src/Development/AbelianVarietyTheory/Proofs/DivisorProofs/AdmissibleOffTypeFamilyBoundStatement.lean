import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBound
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevelBudget.admissible_off_type_level_budget` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdmissibleOffTypeFamilyBound.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.admissible_off_type_family_bound : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.LevelBudget.admissible_off_type_level_budget | exact GlobalTheory.LevelBudget.admissible_off_type_level_budget | (intros; apply GlobalTheory.LevelBudget.admissible_off_type_level_budget <;> assumption)
