import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefUniformBoundsNearPoint
import Mathlib
open Matrix
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.posDef_uniform_bounds_nhds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPosDefUniformBoundsNearPoint.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.posDef_uniform_bounds_near_point : ∀ (Y : Type) [TopologicalSpace Y] (n : Type) [Fintype n] (K : Y → Matrix n n ℂ) (y₀ : Y), ContinuousAt K y₀ → (K y₀).PosDef → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ y in 𝓝 y₀, ∀ u : n → ℂ, c * ‖u‖ ^ 2 ≤ (star u ⬝ᵥ K y *ᵥ u).re ∧ (star u ⬝ᵥ K y *ᵥ u).re ≤ C * ‖u‖ ^ 2 := by
  first | exact @GlobalTheory.posDef_uniform_bounds_nhds | exact GlobalTheory.posDef_uniform_bounds_nhds | (intros; apply GlobalTheory.posDef_uniform_bounds_nhds <;> assumption)
