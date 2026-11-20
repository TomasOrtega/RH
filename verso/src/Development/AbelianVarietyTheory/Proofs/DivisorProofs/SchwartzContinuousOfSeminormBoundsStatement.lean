import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousOfSeminormBounds
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.continuous_schwartz_of_pointwise_of_bounded` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzContinuousOfSeminormBounds.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.schwartz_continuous_of_seminorm_bounds : ∀ {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace S]
    (f : S → SchwartzMap D ℂ),
    (∀ (n : ℕ) (x : D), Continuous fun s => iteratedFDeriv ℝ n (f s) x) →
    (∀ m n : ℕ, ∃ c : S → ℝ, Continuous c ∧ ∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
    Continuous f := by
  first | exact @GlobalTheory.continuous_schwartz_of_pointwise_of_bounded | exact GlobalTheory.continuous_schwartz_of_pointwise_of_bounded | (intros; apply GlobalTheory.continuous_schwartz_of_pointwise_of_bounded <;> assumption)
