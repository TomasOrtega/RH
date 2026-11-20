import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

open MeasureTheory MvPolynomial GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc3

/- English proof (translation)
Introduce `ι _ G hG`. Take `⟨hsmooth, hzero, hnonneg, hpos⟩` from `hG`. Use `set N := Fintype.card ι`. Use `set f : ℝ → ℝ := iteratedDeriv N G with hf`. Establish `hf0 : ∀ x : ℝ, 1 < x → f x = 0`.

Introduce `x hx`. Establish `hev : G =ᶠ[nhds x] (fun _ => (0 : ℝ))` using `by filter_upwards [Ioi_mem_nhds hx] with y hy`. Conclude with `hzero y (le_of_lt hy)`. Rewrite using `[hf, Filter.EventuallyEq.iteratedDeriv_eq N hev]`. Simplify using the standard rewrite rules.

Establish `hfc : Continuous f` using `hsmooth.continuous_iteratedDeriv N (by exact_mod_cast le_top)`. Use `set F : (ι → ℂ) → ℝ := fun w => f (∑ x, ‖w x‖ ^ 2) with hF`. Establish `hFc : Continuous F`. Apply `hfc.comp` to reduce the goal to its premises. Use `fun_prop`.

Establish `hFs : HasCompactSupport F`. Apply `HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 1)` to reduce the goal to its premises. Introduce `w hw`. Rewrite `hw` using `[Metric.mem_closedBall, dist_zero_right, not_le]`. Establish `: ∃ x, 1 < ‖w x‖`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `absurd ((pi_norm_le_iff_of_nonneg zero_le_one).2 h) (not_le.2 hw)`. Take `⟨x, hx⟩` from `this`. Apply `hf0` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `hFn : 0 ≤ F` using `fun w => hnonneg _`. Establish `hF0 : F 0 ≠ 0`. Simplify using `only [hF, Pi.zero_apply, norm_zero]`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]`.

Conclude with `ne_of_gt hpos`. Conclude with `ne_of_gt (hFc.integral_pos_of_hasCompactSupport_nonneg_nonzero hFs hFn hF0)`.
-/
theorem stConst_holds : StConst := by
  intro ι _ G hG
  obtain ⟨hsmooth, hzero, hnonneg, hpos⟩ := hG
  set N := Fintype.card ι
  set f : ℝ → ℝ := iteratedDeriv N G with hf

  have hf0 : ∀ x : ℝ, 1 < x → f x = 0 := by
    intro x hx
    have hev : G =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hzero y (le_of_lt hy)
    rw [hf, Filter.EventuallyEq.iteratedDeriv_eq N hev]
    simp
  have hfc : Continuous f := hsmooth.continuous_iteratedDeriv N (by exact_mod_cast le_top)
  set F : (ι → ℂ) → ℝ := fun w => f (∑ x, ‖w x‖ ^ 2) with hF
  have hFc : Continuous F := by
    apply hfc.comp
    fun_prop
  have hFs : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 1)
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    have : ∃ x, 1 < ‖w x‖ := by
      by_contra h
      push_neg at h
      exact absurd ((pi_norm_le_iff_of_nonneg zero_le_one).2 h) (not_le.2 hw)
    obtain ⟨x, hx⟩ := this
    apply hf0
    calc (1 : ℝ) < ‖w x‖ ^ 2 := by nlinarith
      _ ≤ ∑ y, ‖w y‖ ^ 2 :=
        Finset.single_le_sum (f := fun y => ‖w y‖ ^ 2) (fun y _ => by positivity) (Finset.mem_univ x)
  have hFn : 0 ≤ F := fun w => hnonneg _
  have hF0 : F 0 ≠ 0 := by
    simp only [hF, Pi.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact ne_of_gt hpos
  exact ne_of_gt (hFc.integral_pos_of_hasCompactSupport_nonneg_nonzero hFs hFn hF0)

end GlobalTheory.PsCo.Pc3
