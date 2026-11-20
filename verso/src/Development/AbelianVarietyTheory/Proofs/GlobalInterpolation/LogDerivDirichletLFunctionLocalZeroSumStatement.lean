import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivDirichletLFunctionLocalZeroSum
import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LLocal.logDeriv_LFunction_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLogDerivDirichletLFunctionLocalZeroSum.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.LLocal.logDeriv_LFunction_local | exact GlobalTheory.LLocal.logDeriv_LFunction_local | (intros; apply GlobalTheory.LLocal.logDeriv_LFunction_local <;> assumption)
