import Mathlib

namespace GlobalTheory.DerivativeOfAdditiveContinuous

/- English proof (translation)
Take `⟨δ, hδ, hball⟩` from `Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)`. Use `set η := δ / 2 with hη`. Establish `hη0 : 0 < η` using `by positivity`. Use `set c := ∫ t in (0 : ℝ)..η, χ t with hcdef`. Establish `hc0 : c ≠ 0`.

Establish `hsplit : c = (η : ℂ) + ∫ t in (0 : ℝ)..η, (χ t - 1)`. Rewrite using `[hcdef, intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]`. Simplify using the standard rewrite rules. Establish `hbound : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ ≤ 1 / 2 * |η - 0|`. Apply `intervalIntegral.norm_integral_le_of_norm_le_const` to reduce the goal to its premises.

Introduce `t ht`. Rewrite `ht` using `[Set.uIoc_of_le hη0.le]`. Establish `h1 : dist t 0 < δ`. Rewrite using `[Real.dist_eq, sub_zero, abs_of_pos ht.1]`. Combine the linear relations using `[ht.2]`.

Establish `h2` using `hball t h1`. Rewrite `h2` using `[dist_eq_norm, h0]`. Conclude with `h2.le`. Introduce `hzero`. Rewrite `hzero` using `[hsplit]`.

Establish `h3 : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ = η`. Rewrite using `[eq_neg_of_add_eq_zero_right hzero, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]`. Rewrite `hbound` using `[h3, sub_zero, abs_of_pos hη0]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, χ t with hF`.

Establish `hFd : ∀ x, HasDerivAt F (χ x) x` using `fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt`. Establish `hrep : ∀ x, χ x * c = F (x + η) - F x`. Introduce `x`. Establish `h1 : ∫ t in (0 : ℝ)..η, χ (x + t) = χ x * c`. Simplify using `only [hadd]`.

Rewrite using `[intervalIntegral.integral_const_mul]`. Establish `h2 : ∫ t in (0 : ℝ)..η, χ (x + t) = ∫ t in x..(x + η), χ t`. Rewrite using `[intervalIntegral.integral_comp_add_left]`. Simplify using the standard rewrite rules. Rewrite using `[← h1, h2, hF]`.

Simplify using `only`. Rewrite using `[intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]`. Establish `hdiff : ∀ x, DifferentiableAt ℝ χ x`. Introduce `x`. Establish `hχ : χ = fun y => (F (y + η) - F y) / c`.

Use function extensionality and compare the values at `y`. Rewrite using `[← hrep y, mul_div_cancel_right₀ _ hc0]`. Rewrite using `[hχ]`. Conclude with `(((hFd (x + η)).comp_add_const x η).sub (hFd x)).differentiableAt.div_const c`. Establish `hd0 : HasDerivAt χ (deriv χ 0) (s - s)`.

Rewrite using `[sub_self]`. Conclude with `(hdiff 0).hasDerivAt`. Establish `hcomp : HasDerivAt (fun y => χ (y - s)) (deriv χ 0) s` using `hd0.comp_sub_const s s`. Establish `hmul` using `hcomp.const_mul (χ s)`. Establish `hfun : (fun y => χ s * χ (y - s)) = χ`.

Use function extensionality and compare the values at `y`. Rewrite using `[← hadd]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hmul` using `[hfun]`.

Rewrite using `[mul_comm]`. Conclude with `hmul`.
-/
theorem hasDerivAt_of_continuous_of_map_add (χ : ℝ → ℂ) (hc : Continuous χ)
    (hadd : ∀ s t : ℝ, χ (s + t) = χ s * χ t) (h0 : χ (0 : ℝ) = (1 : ℂ)) (s : ℝ) :
    HasDerivAt χ (deriv χ (0 : ℝ) * χ s) s := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)
  set η := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  set c := ∫ t in (0 : ℝ)..η, χ t with hcdef
  have hc0 : c ≠ 0 := by
    have hsplit : c = (η : ℂ) + ∫ t in (0 : ℝ)..η, (χ t - 1) := by
      rw [hcdef, intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
      simp
    have hbound : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ ≤ 1 / 2 * |η - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hη0.le] at ht
      have h1 : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        linarith [ht.2]
      have h2 := hball t h1
      rw [dist_eq_norm, h0] at h2
      exact h2.le
    intro hzero
    rw [hsplit] at hzero
    have h3 : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ = η := by
      rw [eq_neg_of_add_eq_zero_right hzero, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hη0]
    rw [h3, sub_zero, abs_of_pos hη0] at hbound
    linarith
  set F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, χ t with hF
  have hFd : ∀ x, HasDerivAt F (χ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hrep : ∀ x, χ x * c = F (x + η) - F x := by
    intro x
    have h1 : ∫ t in (0 : ℝ)..η, χ (x + t) = χ x * c := by
      simp only [hadd]
      rw [intervalIntegral.integral_const_mul]
    have h2 : ∫ t in (0 : ℝ)..η, χ (x + t) = ∫ t in x..(x + η), χ t := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    rw [← h1, h2, hF]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have hdiff : ∀ x, DifferentiableAt ℝ χ x := by
    intro x
    have hχ : χ = fun y => (F (y + η) - F y) / c := by
      funext y
      rw [← hrep y, mul_div_cancel_right₀ _ hc0]
    rw [hχ]
    exact (((hFd (x + η)).comp_add_const x η).sub (hFd x)).differentiableAt.div_const c
  have hd0 : HasDerivAt χ (deriv χ 0) (s - s) := by
    rw [sub_self]
    exact (hdiff 0).hasDerivAt
  have hcomp : HasDerivAt (fun y => χ (y - s)) (deriv χ 0) s := hd0.comp_sub_const s s
  have hmul := hcomp.const_mul (χ s)
  have hfun : (fun y => χ s * χ (y - s)) = χ := by
    funext y
    rw [← hadd]
    congr 1
    ring
  rw [hfun] at hmul
  rw [mul_comm]
  exact hmul

end GlobalTheory.DerivativeOfAdditiveContinuous
