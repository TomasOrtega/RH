import Mathlib

open Complex MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hcont : ContinuousOn f {s : ℂ | s.re < c}` using `hf.continuousOn`. Establish `hvert : ∀ x : ℝ, x < c → IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume 0 (2 * Real.pi)`. Introduce `x hx`. Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Use `hcont.comp (by fun_prop) ?_` and prove the remaining obligations.

Introduce `y _`. Simplify using `[hx]`. Establish `hhor : ∀ (x₁ x₂ : ℝ), x₁ ≤ x₂ → x₂ < c → IntervalIntegrable (fun x : ℝ => f (x : ℂ)) volume x₁ x₂`. Introduce `x₁ x₂ h12 h2`. Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises.

Use `hcont.comp (by fun_prop) ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Set.uIcc_of_le h12]`. Simplify using `only [Set.mem_setOf_eq, ofReal_re]`. Combine the linear relations using `[hx.2]`.

Establish `hVim : ∀ x : ℝ, x < c → 0 ≤ (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x + y * I)).im`. Introduce `x hx`. Establish `h2pi : (0:ℝ) ≤ 2 * Real.pi` using `by positivity`. Establish `hc` using `Complex.imCLM.intervalIntegral_comp_comm (hvert x hx)`. Simplify using `only [Complex.imCLM_apply] at hc`.

Rewrite using `[← hc]`. Apply `intervalIntegral.integral_nonneg h2pi` to reduce the goal to its premises. Introduce `y _`. Conclude with `(hpos _ (by simp [hx])).le`. Establish `key : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → x₂ < c → (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₁ + y * I)).im = (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₂ + y * I)).im + m * (x₂ - x₁)`.

Introduce `x₁ x₂ h12 h2c`. Establish `hrect` using `Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x₁ : ℂ) ((x₂ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * I) ?_`. Simplify using `only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, ofReal_zero] at hrect`. Establish `htop : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I)) = (∫ x : ℝ in x₁..x₂, f (x : ℂ)) + (m : ℂ) * ((x₂ - x₁ : ℝ) : ℂ)`. Establish `hc : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I)) = ∫ x : ℝ in x₁..x₂, (f (x : ℂ) + m)`.

Apply `intervalIntegral.integral_congr` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Set.uIcc_of_le h12]`. Establish `hxc : (x : ℂ).re < c` using `by simp; linarith [hx.2]`. Simplify using `only`.

Rewrite using `[← hper _ hxc]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, intervalIntegral.integral_add (hhor x₁ x₂ h12 h2c) intervalIntegrable_const, intervalIntegral.integral_const]`.

Simplify using `[mul_comm]`. Rewrite `hrect` using `[htop]`. Establish `hre` using `congrArg Complex.re hrect`. Simplify using `at hre`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `hf.mono` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[Complex.mem_reProdIm]`. Simplify using `only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hz`. Rewrite `hz` using `[Set.uIcc_of_le h12]`.

Use `show z.re < c`. Combine the linear relations using `[hz.1.2]`. Assume the negation of the conclusion as `hm`. Use `push_neg at hm`. Establish `hm1 : (m : ℝ) ≤ -1` using `by exact_mod_cast (by omega : m ≤ -1)`.

Use `set a := (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f ((c - 1 : ℝ) + y * I)).im with ha`. Establish `ha0 : 0 ≤ a` using `hVim (c - 1) (by linarith)`. Establish `h1` using `key (c - 1 - (a + 1)) (c - 1) (by linarith) (by linarith)`. Establish `h2` using `hVim (c - 1 - (a + 1)) (by linarith)`. Rewrite `h2` using `[h1]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hm1 (by linarith : (0:ℝ) ≤ a + 1)]`.
-/
theorem periodic_strip_shift_nonneg (c : ℝ) (f : ℂ → ℂ) (m : ℤ)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < c})
    (hper : ∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m)
    (hpos : ∀ s : ℂ, s.re < c → 0 < (f s).im) : 0 ≤ m := by
  have hcont : ContinuousOn f {s : ℂ | s.re < c} := hf.continuousOn
  have hvert : ∀ x : ℝ, x < c → IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume 0 (2 * Real.pi) := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro y _
    simp [hx]
  have hhor : ∀ (x₁ x₂ : ℝ), x₁ ≤ x₂ → x₂ < c → IntervalIntegrable (fun x : ℝ => f (x : ℂ)) volume x₁ x₂ := by
    intro x₁ x₂ h12 h2
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le h12] at hx
    simp only [Set.mem_setOf_eq, ofReal_re]
    linarith [hx.2]
  have hVim : ∀ x : ℝ, x < c → 0 ≤ (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x + y * I)).im := by
    intro x hx
    have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
    have hc := Complex.imCLM.intervalIntegral_comp_comm (hvert x hx)
    simp only [Complex.imCLM_apply] at hc
    rw [← hc]
    apply intervalIntegral.integral_nonneg h2pi
    intro y _
    exact (hpos _ (by simp [hx])).le
  have key : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → x₂ < c →
      (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₁ + y * I)).im
        = (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₂ + y * I)).im + m * (x₂ - x₁) := by
    intro x₁ x₂ h12 h2c
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x₁ : ℂ)
      ((x₂ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * I) ?_
    · simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, ofReal_zero] at hrect
      have htop : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
          = (∫ x : ℝ in x₁..x₂, f (x : ℂ)) + (m : ℂ) * ((x₂ - x₁ : ℝ) : ℂ) := by
        have hc : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
            = ∫ x : ℝ in x₁..x₂, (f (x : ℂ) + m) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le h12] at hx
          have hxc : (x : ℂ).re < c := by simp; linarith [hx.2]
          simp only
          rw [← hper _ hxc]
          congr 1
          push_cast
          ring
        rw [hc, intervalIntegral.integral_add (hhor x₁ x₂ h12 h2c) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp [mul_comm]
      rw [htop] at hrect
      have hre := congrArg Complex.re hrect
      simp at hre
      linarith
    · apply hf.mono
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      simp only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hz
      rw [Set.uIcc_of_le h12] at hz
      show z.re < c
      linarith [hz.1.2]
  by_contra hm
  push_neg at hm
  have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
  set a := (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f ((c - 1 : ℝ) + y * I)).im with ha
  have ha0 : 0 ≤ a := hVim (c - 1) (by linarith)
  have h1 := key (c - 1 - (a + 1)) (c - 1) (by linarith) (by linarith)
  have h2 := hVim (c - 1 - (a + 1)) (by linarith)
  rw [h1] at h2
  nlinarith [mul_le_mul_of_nonneg_right hm1 (by linarith : (0:ℝ) ≤ a + 1)]

end GlobalTheory
