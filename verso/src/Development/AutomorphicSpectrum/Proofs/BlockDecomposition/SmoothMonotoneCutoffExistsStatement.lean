import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMonotoneCutoffExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSmoothMonotoneCutoffExists.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.smooth_monotone_cutoff_exists : ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut | exact GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut | (intros; apply GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut <;> assumption)
