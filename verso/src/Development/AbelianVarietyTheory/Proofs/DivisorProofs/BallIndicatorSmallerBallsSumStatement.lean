import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallIndicatorSmallerBallsSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
open ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBallIndicatorSmallerBallsSum.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.ball_indicator_smaller_balls_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s S : kˣ), ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (S : k) → ∃ T : Finset k, T.Nonempty ∧ (∀ t ∈ T, ValuativeRel.valuation k t ≤ ValuativeRel.valuation k (S : k)) ∧ ∀ c x : k, (GlobalTheory.PrinTwo.ball c S).indicator (1 : k → ℂ) x = ∑ t ∈ T, (GlobalTheory.PrinTwo.ball (c + t) s).indicator 1 x := by
  first | exact @GlobalTheory.PrinTwo.BallCover.indicator_ball_eq_sum | exact GlobalTheory.PrinTwo.BallCover.indicator_ball_eq_sum | (intros; apply GlobalTheory.PrinTwo.BallCover.indicator_ball_eq_sum <;> assumption)
