import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTendstoOfPointwiseUniformBounds
import Mathlib
open SchwartzMap Filter Topology
open scoped Nat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.schwartz_tendsto_of_pointwise_of_uniform_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzTendstoOfPointwiseUniformBounds.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.schwartz_tendsto_of_pointwise_uniform_bounds : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : ℕ → SchwartzMap V ℂ) (F0 : SchwartzMap V ℂ),
    (∀ v, Tendsto (fun m => F m v) atTop (𝓝 (F0 v))) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ m v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F m) v‖ ≤ C) →
    Tendsto F atTop (𝓝 F0) := by
  first | exact @GlobalTheory.schwartz_tendsto_of_pointwise_of_uniform_bound | exact GlobalTheory.schwartz_tendsto_of_pointwise_of_uniform_bound | (intros; apply GlobalTheory.schwartz_tendsto_of_pointwise_of_uniform_bound <;> assumption)
