import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLowerBoundNearInjective
import Mathlib
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformLowerBoundNearInjective.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.uniform_lower_bound_near_injective : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm → ∀ (c : P) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → Function.Injective (A c) → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  first | exact @GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | exact GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | (intros; apply GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective <;> assumption)
