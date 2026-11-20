import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAnalyticGrowthSchwartz
import Mathlib
open SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExpTypeDense.dense_expType` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDenseAnalyticGrowthSchwartz.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.dense_analytic_growth_schwartz : (∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W],
      Dense {φ : SchwartzMap W ℂ | HasCompactSupport (⇑φ)}) →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {ψ : SchwartzMap V ℂ | ∃ A ρ : ℝ, ∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j} := by
  first | exact @GlobalTheory.ExpTypeDense.dense_expType | exact GlobalTheory.ExpTypeDense.dense_expType | (intros; apply GlobalTheory.ExpTypeDense.dense_expType <;> assumption)
