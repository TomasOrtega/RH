import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogOfExpContinuity

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.pathLog_variation_continuousAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogOfExpContinuity.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.log_of_exp_continuity : ∀ (B : Type) [TopologicalSpace B] (b₀ : B) (V : Set B) (a : B × ℝ → ℂ), V ∈ nhds b₀ → ContinuousOn (fun q => Complex.exp (a q)) (V ×ˢ Set.Icc (0 : ℝ) 1) → (∀ b ∈ V, ContinuousOn (fun x : ℝ => a (b, x)) (Set.Icc 0 1)) → ContinuousAt (fun b => a (b, 1) - a (b, 0)) b₀ := by
  first | exact @GlobalTheory.pathLog_variation_continuousAt | exact GlobalTheory.pathLog_variation_continuousAt | (intros; apply GlobalTheory.pathLog_variation_continuousAt <;> assumption)
