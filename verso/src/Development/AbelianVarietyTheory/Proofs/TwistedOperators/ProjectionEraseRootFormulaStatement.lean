import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionEraseRootFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.pr_eq_pr_erase_add_rt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FProjectionEraseRootFormula.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.projection_erase_root_formula : ∀ {k : ℕ} {T : Finset (SV k)} {u : SV k}, IsPar T → u ∈ T → ∀ x : A0 k,
  pr T x = pr (T.erase u) x + (⟪rt T u, x⟫_ℝ / ‖rt T u‖ ^ 2) • rt T u := by
  first | exact @GlobalTheory.pr_eq_pr_erase_add_rt | exact GlobalTheory.pr_eq_pr_erase_add_rt | (intros; apply GlobalTheory.pr_eq_pr_erase_add_rt <;> assumption)
