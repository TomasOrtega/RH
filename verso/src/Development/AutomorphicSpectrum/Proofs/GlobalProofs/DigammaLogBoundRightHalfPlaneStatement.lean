import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlane
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FDigammaLogBoundRightHalfPlane.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.digamma_log_bound_right_half_plane : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  first | exact @GlobalTheory.CompanionTheory.DigammaBound.digamma_bound | exact GlobalTheory.CompanionTheory.DigammaBound.digamma_bound | (intros; apply GlobalTheory.CompanionTheory.DigammaBound.digamma_bound <;> assumption)
