import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianQuadraticFormSchwartzBounds
import Mathlib
open SchwartzMap Filter Topology
open scoped Nat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussianQuadraticFormSchwartzBounds.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.gaussian_quadratic_form_schwartz_bounds : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∀ (b k : ℕ) (B : ℝ), ∃ C : ℝ, ∀ x : V,
      ‖x‖ ^ k * Real.exp (B * ‖x‖) * ‖iteratedFDeriv ℝ b (fun y => Complex.exp (-(Q y y))) x‖ ≤ C := by
  first | exact @GlobalTheory.gauss_weighted_iteratedFDeriv_bounded | exact GlobalTheory.gauss_weighted_iteratedFDeriv_bounded | (intros; apply GlobalTheory.gauss_weighted_iteratedFDeriv_bounded <;> assumption)
