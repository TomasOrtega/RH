import Mathlib

open MeasureTheory FourierTransform

/- English proof (translation)
Introduce `G hG hc h`. Establish `hF : 𝓕 G = 0`. Use function extensionality and compare the values at `w`. Establish `h1` using `h (-w)`. Rewrite using `[Real.fourier_real_eq_integral_exp_smul]`.

Simplify using `only [Pi.zero_apply]`. Rewrite using `[← h1]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_comm]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : Integrable (𝓕 G)` using `by rw [hF]; exact integrable_zero _ _ _`. Establish `key` using `hG.fourierInv_fourier_eq hint hc`.

Rewrite using `[← key, hF]`. Simplify using `[Real.fourierInv_eq']`.
-/
theorem UpperTheory.eq_zero_at_one_of_fourierIntegral_eq_zero :
    ∀ (G : ℝ → ℂ), MeasureTheory.Integrable G → ContinuousAt G 1 →
        (∀ u : ℝ, ∫ y : ℝ, G y * Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) = 0) → G 1 = 0 := by
  intro G hG hc h
  have hF : 𝓕 G = 0 := by
    funext w
    have h1 := h (-w)
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [Pi.zero_apply]
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hint : Integrable (𝓕 G) := by rw [hF]; exact integrable_zero _ _ _
  have key := hG.fourierInv_fourier_eq hint hc
  rw [← key, hF]
  simp [Real.fourierInv_eq']
