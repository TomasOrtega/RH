import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundLeftRegion
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlaneStatement
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FDigammaLogBoundLeftRegion.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.digamma_log_bound_left_region : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 → (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) → ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  first | exact @GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left | exact GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left | (intros; apply GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left <;> assumption)
