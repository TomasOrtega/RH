import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMonicSquarefreeUnitConstPolysGe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCardMonicSquarefreeUnitConstPolysGe.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N → (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  first | exact @GlobalTheory.BadShare.card_sqSet_ge | exact GlobalTheory.BadShare.card_sqSet_ge | (intros; apply GlobalTheory.BadShare.card_sqSet_ge <;> assumption)
