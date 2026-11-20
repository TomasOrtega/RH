import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

/- English proof (translation)
Conclude with `VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _`.
-/
lemma norm_fourier_le_integral_norm {d : ℕ} (g : E d → ℂ) (ξ : E d) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/- English proof (translation)
Simplify using `[om]`.
-/
lemma om_zero {d : ℕ} (s : ℝ) (ξ : E d) : om s 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
  simp [om]

/- English proof (translation)
Introduce `d g hg hgs`. Unfold `Hs nrm`. Establish `hint : MeasureTheory.Integrable g` using `hg.integrable_of_hasCompactSupport hgs`. Use `set B : ℝ := ∫ x, ‖g x‖ with hB`. Establish `hBnn : 0 ≤ B` using `MeasureTheory.integral_nonneg fun x => norm_nonneg _`.

Establish `hI : MeasureTheory.Integrable (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2))`. Apply `integrable_rpow_neg_one_add_norm_sq` to reduce the goal to its premises. Establish `: (Module.finrank ℝ (E d) : ℝ) = d` using `by simp`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hI2` using `(hI.const_mul (B ^ 2)).hasFiniteIntegral`. Use `lt_of_le_of_lt (MeasureTheory.lintegral_mono fun ξ => ?_) hI2` and prove the remaining obligations. Establish `ha : 0 < 1 + ‖ξ‖ ^ 2` using `by positivity`. Establish `hom : om (-(d : ℝ) - 1) 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)` using `by simp [om]`. Establish `hsq : ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul ha.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ‖𝓕 g ξ‖ₑ ≤ ENNReal.ofReal B`.

Rewrite using `[← ofReal_norm_eq_enorm]`. Conclude with `ENNReal.ofReal_le_ofReal (norm_fourier_le_integral_norm g ξ)`. Establish `h2 : ‖B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)‖ₑ = ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2))`. Rewrite using `[← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]`. Rewrite using `[h2, hom]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hBnn, ← ENNReal.ofReal_mul (by positivity), hsq, mul_comm]`.
-/
theorem sobolevOfCompactSupport : BaseLevel := by
  intro d g hg hgs
  unfold Hs nrm
  have hint : MeasureTheory.Integrable g := hg.integrable_of_hasCompactSupport hgs
  set B : ℝ := ∫ x, ‖g x‖ with hB
  have hBnn : 0 ≤ B := MeasureTheory.integral_nonneg fun x => norm_nonneg _
  have hI : MeasureTheory.Integrable
      (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    have : (Module.finrank ℝ (E d) : ℝ) = d := by simp
    rw [this]
    linarith
  have hI2 := (hI.const_mul (B ^ 2)).hasFiniteIntegral
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun ξ => ?_) hI2
  have ha : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hom : om (-(d : ℝ) - 1) 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2) := by simp [om]
  have hsq : ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have h1 : ‖𝓕 g ξ‖ₑ ≤ ENNReal.ofReal B := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (norm_fourier_le_integral_norm g ξ)
  have h2 : ‖B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)‖ₑ =
      ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]
  rw [h2, hom]
  calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ‖𝓕 g ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ENNReal.ofReal B ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hBnn,
          ← ENNReal.ofReal_mul (by positivity), hsq, mul_comm]

end ZetaZeros.D.EllReg
