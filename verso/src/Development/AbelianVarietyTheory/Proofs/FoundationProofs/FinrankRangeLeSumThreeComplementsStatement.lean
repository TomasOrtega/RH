import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankRangeLeSumThreeComplements
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.finrank_range_le_three` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFinrankRangeLeSumThreeComplements.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finrank_range_le_sum_three_complements : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (P a b : Module.End ℂ M), Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ (LinearMap.range (a * b * P)) + Module.finrank ℂ (LinearMap.range ((1 - a) * P)) + Module.finrank ℂ (LinearMap.range ((1 - b) * P)) := by
  first | exact @GlobalTheory.BadShare.finrank_range_le_three | exact GlobalTheory.BadShare.finrank_range_le_three | (intros; apply GlobalTheory.BadShare.finrank_range_le_three <;> assumption)
