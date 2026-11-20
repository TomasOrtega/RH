import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakContinuityDerivativeContinuous
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeakDeriv.continuous_iteratedFDeriv_of_weak` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeakContinuityDerivativeContinuous.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.weak_continuity_derivative_continuous : ∀ {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace S]
    (f : S → SchwartzMap D ℂ),
    (∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, Continuous fun s => T (f s)) →
    ∀ (n : ℕ) (x : D), Continuous fun s => iteratedFDeriv ℝ n (f s) x := by
  first | exact @GlobalTheory.WeakDeriv.continuous_iteratedFDeriv_of_weak | exact GlobalTheory.WeakDeriv.continuous_iteratedFDeriv_of_weak | (intros; apply GlobalTheory.WeakDeriv.continuous_iteratedFDeriv_of_weak <;> assumption)
