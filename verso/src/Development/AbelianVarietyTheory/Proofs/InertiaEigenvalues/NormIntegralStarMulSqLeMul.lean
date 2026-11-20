import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ g : X → ℂ, (fun x => star (g x) * g x) = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ)`. Introduce `g`. Use function extensionality and compare the values at `x`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`.

Both sides reduce to the same expression. Establish `re_eq : ∀ g : X → ℂ, (∫ x, star (g x) * g x ∂μ).re = ∫ x, ‖g x‖ ^ 2 ∂μ`. Introduce `g`. Rewrite using `[key g, integral_complex_ofReal]`. Both sides reduce to the same expression.

Establish `int_sq : ∀ g : X → ℂ, Integrable (fun x => star (g x) * g x) μ → Integrable (fun x => ‖g x‖ ^ 2) μ`. Introduce `g hg`. Rewrite `hg` using `[key g]`. Establish `hr` using `hg.re`. Simplify using `only [RCLike.re_to_complex, Complex.ofReal_re] at hr`.

Conclude with `hr`. Establish `mf : MemLp f (ENNReal.ofReal 2) μ`. Rewrite using `[show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hf).mpr (int_sq f hff)`. Establish `mh : MemLp h (ENNReal.ofReal 2) μ`. Rewrite using `[show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hh).mpr (int_sq h hhh)`.

Establish `hold` using `integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two mf mh`. Simplify using `only [Real.rpow_two] at hold`. Rewrite using `[re_eq f, re_eq h]`. Establish `A0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ` using `integral_nonneg fun x => by positivity`. Establish `B0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ` using `integral_nonneg fun x => by positivity`.

Establish `n1 : ‖∫ x, star (f x) * h x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖h x‖ ∂μ`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[norm_mul, norm_star]`.

Establish `n0 : 0 ≤ ‖∫ x, star (f x) * h x ∂μ‖` using `norm_nonneg _`. Establish `hsq : ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖h x‖ ^ 2 ∂μ)`. Rewrite using `[mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt A0, Real.sq_sqrt B0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_integral_star_mul_sq_le {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hff : Integrable (fun x => star (f x) * f x) μ) (hhh : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  have key : ∀ g : X → ℂ, (fun x => star (g x) * g x) = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    intro g; funext x; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re_eq : ∀ g : X → ℂ, (∫ x, star (g x) * g x ∂μ).re = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    intro g; rw [key g, integral_complex_ofReal]; rfl
  have int_sq : ∀ g : X → ℂ, Integrable (fun x => star (g x) * g x) μ → Integrable (fun x => ‖g x‖ ^ 2) μ := by
    intro g hg; rw [key g] at hg; have hr := hg.re; simp only [RCLike.re_to_complex, Complex.ofReal_re] at hr; exact hr
  have mf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hf).mpr (int_sq f hff)
  have mh : MemLp h (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hh).mpr (int_sq h hhh)
  have hold := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two mf mh
  simp only [Real.rpow_two] at hold
  rw [re_eq f, re_eq h]
  have A0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have B0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have n1 : ‖∫ x, star (f x) * h x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖h x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x; rw [norm_mul, norm_star]
  have n0 : 0 ≤ ‖∫ x, star (f x) * h x ∂μ‖ := norm_nonneg _
  have hsq : ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2
      = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖h x‖ ^ 2 ∂μ) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt A0, Real.sq_sqrt B0]
  calc ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left₀ n0 (n1.trans hold) 2
    _ = _ := hsq

end GlobalTheory
