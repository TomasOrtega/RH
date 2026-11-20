import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaA

noncomputable section

open Complex

namespace PI.SSE

/- English proof (translation)
Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma expo1 (v₁ p₁ A z : ℂ) (hv₁ : v₁ ≠ 0) (hA : A ≠ 0) :
    Real.pi * p₁ / (2 * A * v₁) * (z + v₁) ^ 2 =
      Real.pi * p₁ * (z + v₁ / 2) / A + Real.pi * p₁ / (2 * A * v₁) * z ^ 2 := by
  field_simp
  ring

/- English proof (translation)
Rewrite using `[hI]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma expo2 (v₁ v₂ p₁ p₂ A z : ℂ) (hv₁ : v₁ ≠ 0) (hA : A ≠ 0)
    (hI : I = (p₁ * v₂ - v₁ * p₂) / (2 * A)) :
    Real.pi * p₁ / (2 * A * v₁) * (z + v₂) ^ 2 +
        (-(Real.pi * I * (v₂ / v₁)) - 2 * Real.pi * I * (z / v₁)) =
      Real.pi * p₂ * (z + v₂ / 2) / A + Real.pi * p₁ / (2 * A * v₁) * z ^ 2 := by
  rw [hI]
  field_simp
  ring

/- English proof (translation)
Establish `hc : (((starRingEnd ℂ) v₁ * v₂).im : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr h`. Establish `hsub : (starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂ = 2 * I * (((starRingEnd ℂ) v₁ * v₂).im : ℂ)`. Establish `h1 : v₁ * (starRingEnd ℂ) v₂ = (starRingEnd ℂ) ((starRingEnd ℂ) v₁ * v₂)`. Simplify using `[mul_comm]`. Rewrite using `[h1, Complex.sub_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsub]`. Clear the denominators using the available nonvanishing facts.
-/
lemma I_eq (v₁ v₂ : ℂ) (h : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0) :
    I = ((starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂) /
      (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ)) := by
  have hc : (((starRingEnd ℂ) v₁ * v₂).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  have hsub : (starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂ = 2 * I * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) := by
    have h1 : v₁ * (starRingEnd ℂ) v₂ = (starRingEnd ℂ) ((starRingEnd ℂ) v₁ * v₂) := by
      simp [mul_comm]
    rw [h1, Complex.sub_conj]
    push_cast
    ring
  rw [hsub]
  field_simp

/- English proof (translation)
Introduce `hA hD v₁ v₂ hv₁ hτ h3`. Establish `hAr : 0 < ((starRingEnd ℂ) v₁ * v₂).im`. Establish `h1` using `im_div_eq v₁ v₂`. Establish `h2 : 0 < Complex.normSq v₁` using `Complex.normSq_pos.mpr hv₁`. Rewrite `hτ` using `[h1]`.

Conclude with `(div_pos_iff_of_pos_right h2).mp hτ`. Establish `hA0 : (((starRingEnd ℂ) v₁ * v₂).im : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hAr.ne'`. Take `⟨hdiff, hodd, hone, htau, hder⟩` from `hA (v₂ / v₁) hτ`. Establish `hc : jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) ≠ 0` using `hD (v₂ / v₁) hτ h3`. Establish `h0 : th (v₂ / v₁) 0 = 0`.

Establish `h` using `hodd 0`. Rewrite `h` using `[neg_zero]`. Take the linear combination `h / 2`. Use `⟨fun z => v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp (Real.pi * (starRingEnd ℂ) v₁ / (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2) * th (v₂ / v₁) (z / v₁)), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((Differentiable.cexp (by fun_prop)).mul (hdiff.comp (by fun_prop))).const_mul _`.

Establish `hf : HasDerivAt (fun z : ℂ => cexp (Real.pi * (starRingEnd ℂ) v₁ / (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2)) 0 0`. Establish `h1` using `((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi * (starRingEnd ℂ) v₁ / (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁))).cexp`. Simplify using `using h1`. Establish `h1 : HasDerivAt (th (v₂ / v₁)) (jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁)) (0 / v₁)`. Rewrite using `[zero_div, ← hder]`.

Conclude with `(hdiff 0).hasDerivAt`. Establish `h2 : HasDerivAt (fun z : ℂ => z / v₁) (1 / v₁) 0` using `(hasDerivAt_id (0 : ℂ)).div_const v₁`. Establish `hh` using `h1.comp (0 : ℂ) h2`. Establish `hG` using `(hf.mul hh).const_mul (v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁))`. Use `hG.deriv.trans ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, zero_div, h0, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.exp_zero, one_mul]`. Generalize the expression as in `jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) = c at *`. Clear the denominators using the available nonvanishing facts. Introduce `z`. Simplify using `only`.

Rewrite using `[neg_sq, neg_div, hodd]`. Expand and normalize the polynomial expressions, which then agree. Introduce `z`. Simplify using `only`. Establish `e1 : (z + v₁) / v₁ = z / v₁ + 1` using `by field_simp`.

Rewrite using `[e1, hone, expo1 v₁ ((starRingEnd ℂ) v₁) _ z hv₁ hA0, Complex.exp_add]`. Unfold `qf`. Expand and normalize the polynomial expressions, which then agree. Introduce `z`. Simplify using `only`.

Establish `key` using `expo2 v₁ v₂ ((starRingEnd ℂ) v₁) ((starRingEnd ℂ) v₂) _ z hv₁ hA0 (I_eq v₁ v₂ hAr.ne')`. Rewrite using `[add_div, htau]`. Rewrite using `[show ∀ x y t : ℂ, v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp x * -(cexp y * t)) = -(v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp (x + y) * t)) from fun x y t => by rw [Complex.exp_add]; ring, key, Complex.exp_add]`. Unfold `qf`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genEqOf : GenEqOf := by
  intro hA hD v₁ v₂ hv₁ hτ h3
  have hAr : 0 < ((starRingEnd ℂ) v₁ * v₂).im := by
    have h1 := im_div_eq v₁ v₂
    have h2 : 0 < Complex.normSq v₁ := Complex.normSq_pos.mpr hv₁
    rw [h1] at hτ
    exact (div_pos_iff_of_pos_right h2).mp hτ
  have hA0 : (((starRingEnd ℂ) v₁ * v₂).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hAr.ne'
  obtain ⟨hdiff, hodd, hone, htau, hder⟩ := hA (v₂ / v₁) hτ
  have hc : jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) ≠ 0 := hD (v₂ / v₁) hτ h3
  have h0 : th (v₂ / v₁) 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linear_combination h / 2
  refine ⟨fun z => v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) *
      (cexp (Real.pi * (starRingEnd ℂ) v₁ / (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2) *
        th (v₂ / v₁) (z / v₁)), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Differentiable.cexp (by fun_prop)).mul (hdiff.comp (by fun_prop))).const_mul _
  · have hf : HasDerivAt (fun z : ℂ => cexp (Real.pi * (starRingEnd ℂ) v₁ /
        (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2)) 0 0 := by
      have h1 := ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi * (starRingEnd ℂ) v₁ /
        (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁))).cexp
      simpa using h1
    have h1 : HasDerivAt (th (v₂ / v₁)) (jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁)) (0 / v₁) := by
      rw [zero_div, ← hder]
      exact (hdiff 0).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => z / v₁) (1 / v₁) 0 := (hasDerivAt_id (0 : ℂ)).div_const v₁
    have hh := h1.comp (0 : ℂ) h2
    have hG := (hf.mul hh).const_mul (v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁))
    refine hG.deriv.trans ?_
    simp only [Function.comp_apply, zero_div, h0, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Complex.exp_zero, one_mul]
    generalize jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) = c at *
    field_simp
  · intro z
    simp only
    rw [neg_sq, neg_div, hodd]
    ring
  · intro z
    simp only
    have e1 : (z + v₁) / v₁ = z / v₁ + 1 := by field_simp
    rw [e1, hone, expo1 v₁ ((starRingEnd ℂ) v₁) _ z hv₁ hA0, Complex.exp_add]
    unfold qf
    ring
  · intro z
    simp only
    have key := expo2 v₁ v₂ ((starRingEnd ℂ) v₁) ((starRingEnd ℂ) v₂) _ z hv₁ hA0 (I_eq v₁ v₂ hAr.ne')
    rw [add_div, htau]
    rw [show ∀ x y t : ℂ, v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp x * -(cexp y * t)) =
        -(v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp (x + y) * t)) from
        fun x y t => by rw [Complex.exp_add]; ring, key, Complex.exp_add]
    unfold qf
    ring

end PI.SSE

end
