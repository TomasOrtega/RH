import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConverge
import Mathlib
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FDifferentiableAtLimitOfDirectionalDerivsConverge.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.differentiableAt_limit_of_directional_derivs_converge : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  first | exact @GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional | exact GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional | (intros; apply GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional <;> assumption)
