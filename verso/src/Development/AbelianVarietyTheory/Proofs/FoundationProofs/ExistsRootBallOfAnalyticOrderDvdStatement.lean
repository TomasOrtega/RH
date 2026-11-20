import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.RootDisc.exists_root_disc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsRootBallOfAnalyticOrderDvd.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.exists_root_ball_of_analyticOrder_dvd : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R → AnalyticOnNhd ℂ h (Metric.closedBall c R) → (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.RootDisc.exists_root_disc | exact GlobalTheory.KZ.RootDisc.exists_root_disc | (intros; apply GlobalTheory.KZ.RootDisc.exists_root_disc <;> assumption)
