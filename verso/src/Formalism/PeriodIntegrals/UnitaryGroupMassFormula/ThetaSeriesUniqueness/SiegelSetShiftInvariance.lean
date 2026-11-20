import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.Complete

noncomputable section

namespace PI.SSU

open Complex

/- English proof (translation)
Introduce `f hf hper w n`. Use `set g : ℂ → ℂ := fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)) with hg`. Establish `hgd : Differentiable ℂ g` using `by show Differentiable ℂ (fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)))`. Conclude with `hf.mul (by fun_prop)`. Establish `hgp : ∀ z, g (z + 1) = g z`.

Introduce `z`. Use `show f (z + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (z + 1))) = f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z))`. Rewrite using `[hper z]`. Use `congr 1`. Rewrite using `[show -(2 * (Real.pi : ℂ) * I * n * (z + 1)) = -(2 * (Real.pi : ℂ) * I * n * z) + -((n : ℂ) * (2 * Real.pi * I)) by ring, Complex.exp_add, Complex.exp_neg ((n : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, inv_one, mul_one]`.

Establish `hvert : ∀ b : ℝ, ∫ x in (0 : ℝ)..1, g (x + b * I) = ∫ x in (0 : ℝ)..1, g x`. Introduce `b`. Establish `hrect` using `Complex.integral_boundary_rect_eq_zero_of_differentiableOn g 0 (1 + b * I) hgd.differentiableOn`. Establish `h1 : ((1 : ℂ) + b * I).re = 1` using `by simp`. Establish `h2 : ((1 : ℂ) + b * I).im = b` using `by simp`.

Rewrite `hrect` using `[h1, h2, Complex.zero_re, Complex.zero_im]`. Establish `hs : (fun y : ℝ => g (((1 : ℝ) : ℂ) + y * I)) = fun y : ℝ => g (((0 : ℝ) : ℂ) + y * I)`. Use function extensionality and compare the values at `y`. Rewrite using `[← hgp (((0 : ℝ) : ℂ) + y * I)]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hrect` using `[hs, add_sub_cancel_right, sub_eq_zero]`. Simplify using `only [Complex.ofReal_zero, zero_mul, add_zero] at hrect`. Conclude with `hrect.symm`.

Establish `hH : Function.Periodic (fun y : ℝ => g (y + w.im * I)) 1`. Introduce `y`. Use `show g (((y + 1 : ℝ) : ℂ) + w.im * I) = g ((y : ℂ) + w.im * I)`. Rewrite using `[← hgp ((y : ℂ) + w.im * I)]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hw : ∀ x : ℝ, (x : ℂ) + w = ((x + w.re : ℝ) : ℂ) + w.im * I`. Introduce `x`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `show g ((x : ℂ) + w) = g (((x + w.re : ℝ) : ℂ) + w.im * I)`. Rewrite using `[hw x]`.

Use `_ = ∫ x in (0 + w.re)..(1 + w.re), (fun y : ℝ => g (y + w.im * I)) x := intervalIntegral.integral_comp_add_right (fun y : ℝ => g (y + w.im * I)) w.re`. Use `_ = ∫ x in (0 : ℝ)..(0 + 1), (fun y : ℝ => g (y + w.im * I)) x := by`. Rewrite using `[zero_add w.re, add_comm 1 w.re]`. Conclude with `hH.intervalIntegral_add_eq w.re 0`. Use `_ = ∫ x in (0 : ℝ)..1, g (x + w.im * I) := by rw [zero_add]`.

Use `_ = ∫ x in (0 : ℝ)..1, g x := hvert w.im`. Use `_ = coef f n := rfl`.
-/
theorem siegel_set_shift_invariance : ShiftInv := by
  intro f hf hper w n
  set g : ℂ → ℂ := fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)) with hg
  have hgd : Differentiable ℂ g := by
    show Differentiable ℂ (fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)))
    exact hf.mul (by fun_prop)

  have hgp : ∀ z, g (z + 1) = g z := by
    intro z
    show f (z + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (z + 1))) =
      f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z))
    rw [hper z]
    congr 1
    rw [show -(2 * (Real.pi : ℂ) * I * n * (z + 1)) =
        -(2 * (Real.pi : ℂ) * I * n * z) + -((n : ℂ) * (2 * Real.pi * I)) by ring,
      Complex.exp_add, Complex.exp_neg ((n : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, inv_one, mul_one]

  have hvert : ∀ b : ℝ, ∫ x in (0 : ℝ)..1, g (x + b * I) = ∫ x in (0 : ℝ)..1, g x := by
    intro b
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g 0 (1 + b * I)
      hgd.differentiableOn
    have h1 : ((1 : ℂ) + b * I).re = 1 := by simp
    have h2 : ((1 : ℂ) + b * I).im = b := by simp
    rw [h1, h2, Complex.zero_re, Complex.zero_im] at hrect
    have hs : (fun y : ℝ => g (((1 : ℝ) : ℂ) + y * I)) = fun y : ℝ => g (((0 : ℝ) : ℂ) + y * I) := by
      funext y
      rw [← hgp (((0 : ℝ) : ℂ) + y * I)]
      congr 1
      push_cast
      ring
    rw [hs, add_sub_cancel_right, sub_eq_zero] at hrect
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hrect
    exact hrect.symm

  have hH : Function.Periodic (fun y : ℝ => g (y + w.im * I)) 1 := by
    intro y
    show g (((y + 1 : ℝ) : ℂ) + w.im * I) = g ((y : ℂ) + w.im * I)
    rw [← hgp ((y : ℂ) + w.im * I)]
    congr 1
    push_cast
    ring
  have hw : ∀ x : ℝ, (x : ℂ) + w = ((x + w.re : ℝ) : ℂ) + w.im * I := by
    intro x
    apply Complex.ext <;> simp
  calc ∫ x in (0 : ℝ)..1, f (x + w) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (x + w)))
      = ∫ x in (0 : ℝ)..1, (fun y : ℝ => g (y + w.im * I)) (x + w.re) := by
        congr 1
        funext x
        show g ((x : ℂ) + w) = g (((x + w.re : ℝ) : ℂ) + w.im * I)
        rw [hw x]
    _ = ∫ x in (0 + w.re)..(1 + w.re), (fun y : ℝ => g (y + w.im * I)) x :=
        intervalIntegral.integral_comp_add_right (fun y : ℝ => g (y + w.im * I)) w.re
    _ = ∫ x in (0 : ℝ)..(0 + 1), (fun y : ℝ => g (y + w.im * I)) x := by
        rw [zero_add w.re, add_comm 1 w.re]
        exact hH.intervalIntegral_add_eq w.re 0
    _ = ∫ x in (0 : ℝ)..1, g (x + w.im * I) := by rw [zero_add]
    _ = ∫ x in (0 : ℝ)..1, g x := hvert w.im
    _ = coef f n := rfl

end PI.SSU
