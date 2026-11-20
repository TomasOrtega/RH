import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianLogGrowth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFsPotLaplacian
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsInvDerivDecay
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianDecayZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

/- English proof (translation)
Introduce `u F a r hu hr hF heq`. Take `⟨-, hAi, hA0⟩` from `hA`. Take `⟨v, hv_def⟩ : ∃ v : ℂ → ℝ, v = u - a • fsPotPlane` from `⟨_, rfl⟩`. Establish `hφ : ContDiff ℝ 2 (a • fsPotPlane)` using `contDiff_fsPotPlane.const_smul a`. Establish `hv : ContDiff ℝ 2 v` using `hv_def ▸ hu.sub hφ`.

Establish `hρ : 0 < min r 1` using `lt_min hr one_pos`. Establish `hG : ContDiffOn ℝ 2 (F - a • fsPotPlane) (Metric.ball 0 (min r 1))` using `(hF.mono (Metric.ball_subset_ball (min_le_left _ _))).sub hφ.contDiffOn`. Establish `hveq : ∀ y : ℂ, max r⁻¹ 1 < ‖y‖ → v y = (F - a • fsPotPlane) y⁻¹`. Introduce `y hy`. Establish `h1` using `heq y (lt_of_le_of_lt (le_max_left _ _) hy)`.

Establish `h2` using `fsPotPlane_eq (y := y) (by rw [inv_one]; exact lt_of_le_of_lt (le_max_right _ _) hy)`. Simplify using `only [hv_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨C, R₀, hC⟩` from `hD v (F - a • fsPotPlane) (min r 1) (max r⁻¹ 1) hρ hG hveq`. Take `⟨hvi, hv0⟩` from `hZ v C R₀ hv hC`.

Establish `hu' : u = a • fsPotPlane + v` using `by rw [hv_def]; abel`. Establish `hΔ : Δ u = fun y => a * Δ fsPotPlane y + Δ v y`. Use function extensionality and compare the values at `y`. Rewrite using `[hu', ContDiffAt.laplacian_add hφ.contDiffAt hv.contDiffAt, laplacian_smul a contDiff_fsPotPlane.contDiffAt, smul_eq_mul]`. Rewrite using `[hΔ]`.

Use `⟨(hAi.const_mul a).add hvi, ?_⟩` and prove the remaining obligations. Rewrite using `[MeasureTheory.integral_add (hAi.const_mul a) hvi, MeasureTheory.integral_const_mul, hA0, hv0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LaplacianLogGrowth.proof (hA : FsPotLaplacian.Statement) (hD : InvDerivDecay.Statement)
    (hZ : LaplacianDecayZero.Statement) : LaplacianLogGrowth.Statement := by
  intro u F a r hu hr hF heq
  obtain ⟨-, hAi, hA0⟩ := hA
  obtain ⟨v, hv_def⟩ : ∃ v : ℂ → ℝ, v = u - a • fsPotPlane := ⟨_, rfl⟩
  have hφ : ContDiff ℝ 2 (a • fsPotPlane) := contDiff_fsPotPlane.const_smul a
  have hv : ContDiff ℝ 2 v := hv_def ▸ hu.sub hφ
  have hρ : 0 < min r 1 := lt_min hr one_pos
  have hG : ContDiffOn ℝ 2 (F - a • fsPotPlane) (Metric.ball 0 (min r 1)) :=
    (hF.mono (Metric.ball_subset_ball (min_le_left _ _))).sub hφ.contDiffOn
  have hveq : ∀ y : ℂ, max r⁻¹ 1 < ‖y‖ → v y = (F - a • fsPotPlane) y⁻¹ := by
    intro y hy
    have h1 := heq y (lt_of_le_of_lt (le_max_left _ _) hy)
    have h2 := fsPotPlane_eq (y := y) (by rw [inv_one]; exact lt_of_le_of_lt (le_max_right _ _) hy)
    simp only [hv_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
    ring
  obtain ⟨C, R₀, hC⟩ := hD v (F - a • fsPotPlane) (min r 1) (max r⁻¹ 1) hρ hG hveq
  obtain ⟨hvi, hv0⟩ := hZ v C R₀ hv hC
  have hu' : u = a • fsPotPlane + v := by rw [hv_def]; abel
  have hΔ : Δ u = fun y => a * Δ fsPotPlane y + Δ v y := by
    funext y
    rw [hu', ContDiffAt.laplacian_add hφ.contDiffAt hv.contDiffAt,
      laplacian_smul a contDiff_fsPotPlane.contDiffAt, smul_eq_mul]
  rw [hΔ]
  refine ⟨(hAi.const_mul a).add hvi, ?_⟩
  rw [MeasureTheory.integral_add (hAi.const_mul a) hvi, MeasureTheory.integral_const_mul, hA0, hv0]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
