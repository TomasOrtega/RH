import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiveElementaryInequalitiesEventually
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.five_elementary_inequalities_eventually` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiveElementaryInequalitiesEventually.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.eventually_rpow_log_inequalities : ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop, x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧ 11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧ 2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧ 44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  first | exact @GlobalTheory.five_elementary_inequalities_eventually | exact GlobalTheory.five_elementary_inequalities_eventually | (intros; apply GlobalTheory.five_elementary_inequalities_eventually <;> assumption)
