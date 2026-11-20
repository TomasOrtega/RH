import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTruncatedGaussiansWithDensities
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaussMean.Trunc.exists_truncated` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsTruncatedGaussiansWithDensities.lean&line=243#L243)
-/
theorem _root_.GlobalTheory.T.exists_truncated_gaussians_with_densities : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (φ : ℕ → (Fin n → ℂ) → ℝ) (D : ℕ → ℝ → ℝ), (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ k) ∧ HasCompactSupport (φ k) ∧ (∀ y, 0 ≤ φ k y) ∧ IsDens ε (φ k) (D k)) ∧ (∀ y, Monotone (fun k => φ k y) ∧ Filter.Tendsto (fun k => φ k y) Filter.atTop (nhds (gauss y))) ∧ ∀ β : ℝ, β ≠ 0 → Filter.Tendsto (fun k => D k β) Filter.atTop (nhds (gaussDens ε β)) := by
  first | exact @GlobalTheory.GaussMean.Trunc.exists_truncated | exact GlobalTheory.GaussMean.Trunc.exists_truncated | (intros; apply GlobalTheory.GaussMean.Trunc.exists_truncated <;> assumption)
