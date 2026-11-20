import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KillsTranslatesSumMulMeanDifferenceEq
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKillsTranslatesSumMulMeanDifferenceEq.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq : ∀ (L : ℕ) (v : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ), 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x => ‖G x‖) → (Summable fun x => ‖dif L v G x‖) ∧ ∑' x, Φ x * dif L v G x = ∑' x, Φ x * G x := by
  first | exact @GlobalTheory.EisM.kills_sum_dif_eq | exact GlobalTheory.EisM.kills_sum_dif_eq | (intros; apply GlobalTheory.EisM.kills_sum_dif_eq <;> assumption)
