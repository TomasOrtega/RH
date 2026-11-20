import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveQuadraticLowerBound
import Mathlib
open SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPositiveQuadraticLowerBound.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.positive_quadratic_lower_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ), (∀ x, x ≠ 0 → 0 < (Q x x).re) →
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re := by
  first | exact @GlobalTheory.coercive_of_re_pos | exact GlobalTheory.coercive_of_re_pos | (intros; apply GlobalTheory.coercive_of_re_pos <;> assumption)
