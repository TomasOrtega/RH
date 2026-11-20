import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.goodSet_weight_ge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGoodSquarefreeLabelTuplesWeightGe.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.goodSquarefreeLabelTuples_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  first | exact @GlobalTheory.BadShare.goodSet_weight_ge | exact GlobalTheory.BadShare.goodSet_weight_ge | (intros; apply GlobalTheory.BadShare.goodSet_weight_ge <;> assumption)
