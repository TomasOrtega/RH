import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBound
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.divisor_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSquarefreeLabelTorusMassDivisorBound.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧ ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  first | exact @GlobalTheory.BadShare.divisor_bound | exact GlobalTheory.BadShare.divisor_bound | (intros; apply GlobalTheory.BadShare.divisor_bound <;> assumption)
