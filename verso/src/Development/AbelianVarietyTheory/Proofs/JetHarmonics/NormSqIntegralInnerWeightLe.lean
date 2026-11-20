import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Use `set F : Ω → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ‖f x‖ₑ with hF`. Use `set G : Ω → ℝ≥0∞ := fun x => ‖g x‖ₑ with hG`. Establish `hFm : AEMeasurable F ν` using `hp.enorm.mul hf.enorm`. Establish `hGm : AEMeasurable G ν` using `hg.enorm`. Establish `h1 : ‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ₑ ≤ ∫⁻ x, (F * G) x ∂ν`.

Use `(enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)` and prove the remaining obligations. Establish `h : ‖⟪f x, ph x • g x⟫_ℂ‖ ≤ ‖ph x‖ * ‖f x‖ * ‖g x‖`. Use `(norm_inner_le_norm _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[norm_smul]`. Expand and normalize the polynomial expressions, which then agree.

Use `ENNReal.ofReal_le_ofReal h` as an intermediate fact. Rewrite `this` using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]`. Conclude with `this`. Establish `h2` using `ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hFm hGm`. Establish `e1 : (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) = ∫⁻ x, F x ^ (2 : ℝ) ∂ν`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ENNReal.rpow_two]`. Establish `e2 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν) = ∫⁻ x, G x ^ (2 : ℝ) ∂ν`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm, ENNReal.rpow_two]`.

Rewrite using `[e1, e2, ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm]`. Use `(pow_le_pow_left' (h1.trans h2) 2).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `k : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a` using `fun a => by`. Rewrite using `[← ENNReal.rpow_two, ← ENNReal.rpow_mul]`. Evaluate the numerical expressions.

Rewrite using `[mul_pow, k, k]`.
-/
theorem norm_sq_integral_inner_smul_le (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ)
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hp : AEStronglyMeasurable ph ν) :
    ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤
      (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  set F : Ω → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ‖f x‖ₑ with hF
  set G : Ω → ℝ≥0∞ := fun x => ‖g x‖ₑ with hG
  have hFm : AEMeasurable F ν := hp.enorm.mul hf.enorm
  have hGm : AEMeasurable G ν := hg.enorm
  have h1 : ‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ₑ ≤ ∫⁻ x, (F * G) x ∂ν := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    have h : ‖⟪f x, ph x • g x⟫_ℂ‖ ≤ ‖ph x‖ * ‖f x‖ * ‖g x‖ := by
      refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
      rw [norm_smul]; ring
    have := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ofReal_norm_eq_enorm,
      ofReal_norm_eq_enorm] at this
    exact this
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hFm hGm
  have e1 : (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) = ∫⁻ x, F x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← mul_pow, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ENNReal.rpow_two]
  have e2 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν) = ∫⁻ x, G x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm, ENNReal.rpow_two]
  rw [e1, e2, ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm]
  refine (pow_le_pow_left' (h1.trans h2) 2).trans (le_of_eq ?_)
  have k : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  rw [mul_pow, k, k]

end GlobalTheory
