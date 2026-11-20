import Mathlib
open MeasureTheory Filter Topology Set

namespace GlobalTheory

/- English proof (translation)
Introduce `g K c m τ _ hc hg hτ`. Use `set B : ℝ := 2 + ‖τ - Complex.I‖ with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`. Use `set F : ℝ → ℝ := fun S => |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m with hF`. Establish `hpt : ∀ S : ℝ, 0 ≤ S → ∀ t ∈ Set.uIoc (0:ℝ) 1, ‖g (Complex.I + t * (τ - Complex.I) + S * Complex.I)‖ ≤ F S`.

Introduce `S hS t ht`. Rewrite `ht` using `[Set.uIoc_of_le zero_le_one]`. Take `⟨ht0, ht1⟩` from `ht`. Use `set z := Complex.I + t * (τ - Complex.I) + S * Complex.I with hz`. Establish `him : z.im = 1 + t * (τ.im - 1) + S`.

Simplify using `[hz]`. Establish `him1 : 1 + S ≤ z.im`. Rewrite using `[him]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hnorm : 1 + ‖z‖ ≤ B + S`.

Establish `h1 : ‖z‖ ≤ ‖Complex.I‖ + ‖(t:ℂ) * (τ - Complex.I)‖ + ‖(S:ℂ) * Complex.I‖`. Rewrite using `[hz]`. Conclude with `norm_add₃_le`. Establish `h2 : ‖(t:ℂ) * (τ - Complex.I)‖ ≤ ‖τ - Complex.I‖`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) ht1`. Establish `h3 : ‖(S:ℂ) * Complex.I‖ = S`. Rewrite using `[norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]`. Rewrite `h1` using `[Complex.norm_I]`. Rewrite using `[hB]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : Real.exp (-c * z.im) ≤ Real.exp (-c * (1 + S))` using `Real.exp_le_exp.mpr (by nlinarith)`. Establish `hp : (1 + ‖z‖) ^ m ≤ (B + S) ^ m` using `pow_le_pow_left₀ (by positivity) hnorm m`. Combine the equalities or inequalities in the displayed calculation. Establish `hlim : Tendsto F atTop (𝓝 0)`.

Establish `h1 : Tendsto (fun S : ℝ => c * (B + S)) atTop atTop` using `(tendsto_atTop_add_const_left atTop B tendsto_id).const_mul_atTop hc`. Establish `h2` using `((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp h1).const_mul (|K| * (c ^ m)⁻¹ * Real.exp (c * B - c))`. Rewrite `h2` using `[mul_zero]`. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards with S`.

Establish `hcm : c ^ m ≠ 0` using `pow_ne_zero _ hc.ne'`. Establish `hexp : Real.exp (c * B - c) * Real.exp (-(c * (B + S))) = Real.exp (-c * (1 + S))`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Simplify using `only [Function.comp, hF]`.

Rewrite using `[mul_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `squeeze_zero_norm' ?_ hlim` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS`. Use `intervalIntegral.norm_integral_le_of_norm_le_const (hpt S hS)` as an intermediate fact.

Rewrite `this` using `[sub_zero, abs_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem top_side_integral_tendsto_zero : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    Tendsto (fun S : ℝ => ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop (𝓝 0) := by
  intro g K c m τ _ hc hg hτ
  set B : ℝ := 2 + ‖τ - Complex.I‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set F : ℝ → ℝ := fun S => |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m with hF
  have hpt : ∀ S : ℝ, 0 ≤ S → ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖g (Complex.I + t * (τ - Complex.I) + S * Complex.I)‖ ≤ F S := by
    intro S hS t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    set z := Complex.I + t * (τ - Complex.I) + S * Complex.I with hz
    have him : z.im = 1 + t * (τ.im - 1) + S := by
      simp [hz]
    have him1 : 1 + S ≤ z.im := by
      rw [him]; nlinarith
    have hnorm : 1 + ‖z‖ ≤ B + S := by
      have h1 : ‖z‖ ≤ ‖Complex.I‖ + ‖(t:ℂ) * (τ - Complex.I)‖ + ‖(S:ℂ) * Complex.I‖ := by
        rw [hz]; exact norm_add₃_le
      have h2 : ‖(t:ℂ) * (τ - Complex.I)‖ ≤ ‖τ - Complex.I‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      have h3 : ‖(S:ℂ) * Complex.I‖ = S := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
      rw [Complex.norm_I] at h1
      rw [hB]; linarith
    have he : Real.exp (-c * z.im) ≤ Real.exp (-c * (1 + S)) := Real.exp_le_exp.mpr (by nlinarith)
    have hp : (1 + ‖z‖) ^ m ≤ (B + S) ^ m := pow_le_pow_left₀ (by positivity) hnorm m
    calc ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := hg z (by linarith)
      _ ≤ |K| * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m :=
          mul_le_mul (mul_le_mul_of_nonneg_left he (abs_nonneg K)) hp (by positivity) (by positivity)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun S : ℝ => c * (B + S)) atTop atTop :=
      (tendsto_atTop_add_const_left atTop B tendsto_id).const_mul_atTop hc
    have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp h1).const_mul
      (|K| * (c ^ m)⁻¹ * Real.exp (c * B - c))
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards with S
    have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc.ne'
    have hexp : Real.exp (c * B - c) * Real.exp (-(c * (B + S))) = Real.exp (-c * (1 + S)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Function.comp, hF]
    rw [mul_pow]
    calc |K| * (c ^ m)⁻¹ * Real.exp (c * B - c) * (c ^ m * (B + S) ^ m * Real.exp (-(c * (B + S))))
        = |K| * (Real.exp (c * B - c) * Real.exp (-(c * (B + S)))) * ((c ^ m)⁻¹ * c ^ m) * (B + S) ^ m := by ring
      _ = |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m := by rw [hexp, inv_mul_cancel₀ hcm, mul_one]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
  have := intervalIntegral.norm_integral_le_of_norm_le_const (hpt S hS)
  rwa [sub_zero, abs_one, mul_one] at this

end GlobalTheory
