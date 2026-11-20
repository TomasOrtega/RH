import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHolomorphicMorseInequalityUniform
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.morse_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalHolomorphicMorseInequalityUniform.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.local_holomorphic_morse_inequality_uniform : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U → (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧ ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U → ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤ ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by
  first | exact @GlobalTheory.morse_local | exact GlobalTheory.morse_local | (intros; apply GlobalTheory.morse_local <;> assumption)
