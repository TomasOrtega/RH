import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GramDetOptionFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.gram_det_option_orth` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FGramDetOptionFormula.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.gram_det_option_formula : ∀ {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (w0 : A0 k) (y : ι → A0 k) (κ t : ι → ℝ), (∀ i, ⟪y i, w0⟫_ℝ = 0) →
  (Matrix.gram ℝ (fun o : Option ι => o.elim w0 fun i => κ i • y i + t i • w0)).det =
    ‖w0‖ ^ 2 * (∏ i, κ i ^ 2) * (Matrix.gram ℝ y).det := by
  first | exact @GlobalTheory.gram_det_option_orth | exact GlobalTheory.gram_det_option_orth | (intros; apply GlobalTheory.gram_det_option_orth <;> assumption)
