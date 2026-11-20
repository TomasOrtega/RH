import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPeriod

open Matrix

noncomputable section

/- English proof (translation)
Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h1 : l / (2 * Real.pi * Complex.I) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-Complex.I * l)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `Complex.I_mul_I` as an intermediate fact.

Take the linear combination `l * this`. Rewrite using `[h1, Complex.im_ofReal_mul, Complex.norm_exp, Real.log_inv, Real.log_exp]`. Simplify using the standard rewrite rules.
-/
theorem cfac_im (l : ℂ) :
    (l / (2 * Real.pi * Complex.I)).im = (2 * Real.pi)⁻¹ * Real.log ‖Complex.exp l‖⁻¹ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : l / (2 * Real.pi * Complex.I) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-Complex.I * l) := by
    push_cast
    field_simp
    have := Complex.I_mul_I
    linear_combination l * this
  rw [h1, Complex.im_ofReal_mul, Complex.norm_exp, Real.log_inv, Real.log_exp]
  simp

/- English proof (translation)
Use extensionality with `k m`. Simplify using `only [PeriodChartData.period, PeriodChartData.Y, chartImag, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Complex.add_im, Complex.im_sum, Matrix.smul_apply, smul_eq_mul, cuspTime]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.im_mul_ofReal, cfac_im, h j]`.
-/
theorem period_im (D : PeriodChartData) (z : Fin D.n → ℂ) (l : Fin D.a → ℂ)
    (h : ∀ j, Complex.exp (l j) = cuspCoord D.a_le z j) :
    (D.period z l).map Complex.im = D.Y z := by
  ext k m
  simp only [PeriodChartData.period, PeriodChartData.Y, chartImag, Matrix.map_apply,
    Matrix.add_apply, Matrix.sum_apply, Complex.add_im, Complex.im_sum, Matrix.smul_apply,
    smul_eq_mul, cuspTime]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.im_mul_ofReal, cfac_im, h j]

/- English proof (translation)
Introduce `r s τ hs hp`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `congrFun (congrFun hs (Sum.inr i)) (Sum.inr j)` as an intermediate fact. Simplify `this` using `[Matrix.toBlocks₂₂]`.

Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₂]`. Establish `: (τ.toBlocks₂₂).map Complex.im = (τ.map Complex.im).submatrix Sum.inr Sum.inr`. Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₂]`.

Rewrite using `[this]`. Conclude with `hp.submatrix Sum.inr_injective`.
-/
theorem schurQuotientPeriod : SchurQuotientPeriod.Statement := by
  intro r s τ hs hp
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun hs (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂] using this
  · ext i j
    simp [Matrix.toBlocks₂₂]
  · have : (τ.toBlocks₂₂).map Complex.im = (τ.map Complex.im).submatrix Sum.inr Sum.inr := by
      ext i j
      simp [Matrix.toBlocks₂₂]
    rw [this]
    exact hp.submatrix Sum.inr_injective

end

end GroundTheory.Heights₂.Heights.MCPeriod
