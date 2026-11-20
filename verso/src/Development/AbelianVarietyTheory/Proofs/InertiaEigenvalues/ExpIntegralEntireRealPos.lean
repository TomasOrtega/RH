import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Distinguish the cases in `h0 : f = 0`. Simplify using `[h0]`. Establish `ht` using `hR h0`. Rewrite using `[norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]`. Apply `mul_le_mul_of_nonneg_left _ hf` to reduce the goal to its premises.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h1 : (s * (t : ℂ)).re = s.re * t` using `by simp`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_mul_cexp_le_of_abs_le_on_support {s : ℂ} {f t : ℝ} {R : ℝ} (hf : 0 ≤ f) (hR : f ≠ 0 → |t| ≤ R) :
    ‖(f : ℂ) * Complex.exp (s * t)‖ ≤ f * Real.exp (‖s‖ * R) := by
  by_cases h0 : f = 0
  · simp [h0]
  have ht := hR h0
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  apply mul_le_mul_of_nonneg_left _ hf
  apply Real.exp_le_exp.mpr
  have h1 : (s * (t : ℂ)).re = s.re * t := by simp
  rw [h1]
  calc s.re * t ≤ |s.re * t| := le_abs_self _
    _ = |s.re| * |t| := abs_mul _ _
    _ ≤ ‖s‖ * R := mul_le_mul (Complex.abs_re_le_norm s) ht (abs_nonneg _) (norm_nonneg _)

/- English proof (translation)
Take `⟨R, hR⟩` from `hR`. Establish `hmeas : ∀ s : ℂ, Measurable fun y => (f y : ℂ) * Complex.exp (s * t y)`. Introduce `s`. Use `fun_prop`. Establish `hint : ∀ s : ℂ, Integrable (fun y => (f y : ℂ) * Complex.exp (s * t y)) ν`.

Introduce `s`. Use `Integrable.mono' (hfi.mul_const (Real.exp (‖s‖ * R))) (hmeas s).aestronglyMeasurable (ae_of_all _ fun y => norm_mul_cexp_le_of_abs_le_on_support (hf0 y) (hR y))` and prove the remaining obligations. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `s₀`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀) (F := fun s y => (f y : ℂ) * Complex.exp (s * t y)) (F' := fun s y => (f y : ℂ) * (Complex.exp (s * t y) * t y)) (bound := fun y => f y * R * Real.exp ((‖s₀‖ + 1) * R)) (Metric.ball_mem_nhds s₀ one_pos) (Filter. …`.

Conclude with `key.2.differentiableAt`. Distinguish the cases in `h0 : f y = 0`. Simplify using `[h0]`. Establish `ht` using `hR y h0`. Establish `hR0 : 0 ≤ R` using `(abs_nonneg _).trans ht`.

Establish `hs' : ‖s‖ ≤ ‖s₀‖ + 1`. Use `norm_le_norm_add_norm_sub' s s₀` as an intermediate fact. Rewrite `hs` using `[Metric.mem_ball, dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1` using `norm_mul_cexp_le_of_abs_le_on_support (s := s) (hf0 y) (hR y)`.

Rewrite using `[← mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation. Establish `: Real.exp (‖s‖ * R) ≤ Real.exp ((‖s₀‖ + 1) * R)` using `Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs' hR0)`. Use `mul_le_mul_of_nonneg_left this (mul_nonneg (hf0 y) hR0)` as an intermediate fact. Use polynomial arithmetic with `[this]`.

Use `((hasDerivAt_id s).mul_const (t y : ℂ)).cexp` as an intermediate fact. Simplify using `only [id, one_mul] at this`. Conclude with `this.const_mul (f y : ℂ)`. Introduce `r`. Establish `hre : ∀ y, (f y : ℂ) * Complex.exp (r * t y) = ((f y * Real.exp (r * t y) : ℝ) : ℂ)`.

Introduce `y`. Use `push_cast`. Put the polynomial expressions in normal form. Repeatedly rewrite using `[hre]`. Rewrite using `[integral_complex_ofReal]`.

Use `⟨Complex.ofReal_im _, fun hpos => ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.ofReal_re]`. Establish `gint : Integrable (fun y => f y * Real.exp (r * t y)) ν`. Use `hint (r : ℂ)` as an intermediate fact. Rewrite `this` using `[hre]`.

Conclude with `this.re`. Establish `hle : ∀ y, f y * Real.exp (-(|r| * R)) ≤ f y * Real.exp (r * t y)`. Introduce `y`. Distinguish the cases in `h0 : f y = 0`. Simplify using `[h0]`.

Apply `mul_le_mul_of_nonneg_left _ (hf0 y)` to reduce the goal to its premises. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `ht` using `hR y h0`. Establish `: |r * t y| ≤ |r| * R`. Rewrite using `[abs_mul]`.

Conclude with `mul_le_mul_of_nonneg_left ht (abs_nonneg _)`. Combine the linear relations using `[neg_abs_le (r * t y)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_integral_entire_real_pos {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ)
    (hfm : Measurable f) (htm : Measurable t) (hf0 : ∀ y, 0 ≤ f y)
    (hfi : Integrable f ν) (hR : ∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) :
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  obtain ⟨R, hR⟩ := hR
  have hmeas : ∀ s : ℂ, Measurable fun y => (f y : ℂ) * Complex.exp (s * t y) := by
    intro s; fun_prop
  have hint : ∀ s : ℂ, Integrable (fun y => (f y : ℂ) * Complex.exp (s * t y)) ν := by
    intro s
    refine Integrable.mono' (hfi.mul_const (Real.exp (‖s‖ * R))) (hmeas s).aestronglyMeasurable
      (ae_of_all _ fun y => norm_mul_cexp_le_of_abs_le_on_support (hf0 y) (hR y))
  refine ⟨?_, ?_⟩
  · intro s₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
      (F := fun s y => (f y : ℂ) * Complex.exp (s * t y))
      (F' := fun s y => (f y : ℂ) * (Complex.exp (s * t y) * t y))
      (bound := fun y => f y * R * Real.exp ((‖s₀‖ + 1) * R))
      (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable) (hint s₀)
      (by fun_prop : Measurable fun y => (f y : ℂ) * (Complex.exp (s₀ * t y) * t y)).aestronglyMeasurable
      (ae_of_all _ fun y s hs => ?_)
      ((hfi.mul_const R).mul_const _)
      (ae_of_all _ fun y s _ => ?_)
    · exact key.2.differentiableAt
    · by_cases h0 : f y = 0
      · simp [h0]
      have ht := hR y h0
      have hR0 : 0 ≤ R := (abs_nonneg _).trans ht
      have hs' : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' s s₀
        rw [Metric.mem_ball, dist_eq_norm] at hs
        linarith
      have e1 := norm_mul_cexp_le_of_abs_le_on_support (s := s) (hf0 y) (hR y)
      rw [← mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖(f y : ℂ) * Complex.exp (s * t y)‖ * |t y|
          ≤ (f y * Real.exp (‖s‖ * R)) * R := mul_le_mul e1 ht (abs_nonneg _) (mul_nonneg (hf0 y) (Real.exp_pos _).le)
        _ ≤ f y * R * Real.exp ((‖s₀‖ + 1) * R) := by
          have : Real.exp (‖s‖ * R) ≤ Real.exp ((‖s₀‖ + 1) * R) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs' hR0)
          have := mul_le_mul_of_nonneg_left this (mul_nonneg (hf0 y) hR0)
          nlinarith [this]
    · have := ((hasDerivAt_id s).mul_const (t y : ℂ)).cexp
      simp only [id, one_mul] at this
      exact this.const_mul (f y : ℂ)
  · intro r
    have hre : ∀ y, (f y : ℂ) * Complex.exp (r * t y) = ((f y * Real.exp (r * t y) : ℝ) : ℂ) := by
      intro y; push_cast; ring_nf
    simp_rw [hre]
    rw [integral_complex_ofReal]
    refine ⟨Complex.ofReal_im _, fun hpos => ?_⟩
    rw [Complex.ofReal_re]
    have gint : Integrable (fun y => f y * Real.exp (r * t y)) ν := by
      have := hint (r : ℂ)
      simp_rw [hre] at this
      exact this.re
    have hle : ∀ y, f y * Real.exp (-(|r| * R)) ≤ f y * Real.exp (r * t y) := by
      intro y
      by_cases h0 : f y = 0
      · simp [h0]
      apply mul_le_mul_of_nonneg_left _ (hf0 y)
      apply Real.exp_le_exp.mpr
      have ht := hR y h0
      have : |r * t y| ≤ |r| * R := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      linarith [neg_abs_le (r * t y)]
    calc 0 < (∫ y, f y ∂ν) * Real.exp (-(|r| * R)) := mul_pos hpos (Real.exp_pos _)
      _ = ∫ y, f y * Real.exp (-(|r| * R)) ∂ν := (integral_mul_const _ _).symm
      _ ≤ ∫ y, f y * Real.exp (r * t y) ∂ν := integral_mono (hfi.mul_const _) gint hle

end GlobalTheory
