import Formalism.HermitianCurvature.HermitianCurvatureProofs.MomentIntegrable
import Formalism.HermitianCurvature.CompositeFormulaLevelZero

open MeasureTheory Real Complex
open scoped FourierTransform ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

/- English proof (translation)
Rewrite using `[Real.fourier_eq]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]`. Use `congr 1`. Unfold `Formalism.FourierDecayAlt.P5.fsv`.

Use `congr 1`. Rewrite using `[Complex.inner]`. Establish `hπ : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `e1 : s * t - conj s * conj t = ((2 * (s * t).im : ℝ) : ℂ) * I`. Rewrite using `[← map_mul, Complex.sub_conj]`.

Rewrite using `[e1]`. Use `congr 1`. Use `push_cast`. Establish `e2 : (-(I * conj s) / (π : ℂ) * conj t).re = -((s * t).im) / π`. Rewrite using `[div_mul_eq_mul_div, Complex.div_ofReal_re]`.

Simplify using `[Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_fsv_eq_fourier (D : ℂ → ℂ) (s : ℂ) :
    ∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t = 𝓕 D (-(I * conj s) / (π : ℂ)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1
  unfold Formalism.FourierDecayAlt.P5.fsv
  congr 1
  rw [Complex.inner]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : s * t - conj s * conj t = ((2 * (s * t).im : ℝ) : ℂ) * I := by
    rw [← map_mul, Complex.sub_conj]
  rw [e1]
  congr 1
  push_cast
  have e2 : (-(I * conj s) / (π : ℂ) * conj t).re = -((s * t).im) / π := by
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [e2]
  push_cast
  field_simp

/- English proof (translation)
Use `fourier_smooth D m C hD fun w => ?_` and prove the remaining obligations. Rewrite using `[Complex.finrank_real_complex]`. Use `set s : ℂ := -(I * π * conj w) with hs`. Establish `hw : w = -(I * conj s) / (π : ℂ)`. Establish `hπ : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Rewrite using `[hs]`. Simplify using `only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]`. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Simplify using `[Complex.I_sq]`.

Establish `hns : ‖s‖ = π * ‖w‖`. Rewrite using `[hs, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]`. Establish `h` using `hdec s`. Rewrite `h` using `[integral_fsv_eq_fourier, ← hw]`. Use `h.trans ?_` and prove the remaining obligations.

Establish `hC : 0 ≤ C`. Establish `h0` using `(norm_nonneg _).trans (hdec 0)`. Conclude with `nonneg_of_mul_nonneg_left h0 (by positivity)`. Establish `e : (-((m : ℝ) + ((2 : ℕ) : ℝ) + 1)) = -((m : ℝ) + 3)` using `by push_cast; ring`. Rewrite using `[e]`.

Use `mul_le_mul_of_nonneg_left ?_ hC` and prove the remaining obligations. Use `Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])` and prove the remaining obligations. Rewrite using `[hns]`. Use polynomial arithmetic with `[Real.pi_gt_three, norm_nonneg w]`.
-/
theorem smooth_bounded_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  refine fourier_smooth D m C hD fun w => ?_
  rw [Complex.finrank_real_complex]
  set s : ℂ := -(I * π * conj w) with hs
  have hw : w = -(I * conj s) / (π : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hs]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hns : ‖s‖ = π * ‖w‖ := by
    rw [hs, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have h := hdec s
  rw [integral_fsv_eq_fourier, ← hw] at h
  refine h.trans ?_
  have hC : 0 ≤ C := by
    have h0 := (norm_nonneg _).trans (hdec 0)
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have e : (-((m : ℝ) + ((2 : ℕ) : ℝ) + 1)) = -((m : ℝ) + 3) := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rw [hns]
  nlinarith [Real.pi_gt_three, norm_nonneg w]

end Formalism.FourierDecayAlt.P5.HerC.Fou
