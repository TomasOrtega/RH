import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm

noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

/- English proof (translation)
Use `set F : ι → (I → ℝ) → ℂ := fun j y => a j * ((p y : ℂ) * term n s (e j) y) with hF`. Establish `hpm : AEStronglyMeasurable (fun y => (p y : ℂ)) volume` using `(Complex.measurable_ofReal.comp hp).aestronglyMeasurable`. Establish `hpb : ∀ᵐ y ∂(volume : Measure (I → ℝ)), ‖(p y : ℂ)‖ ≤ 1`. Use `Filter.Eventually.of_forall fun y => ?_` and prove the remaining obligations. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]`.

Conclude with `hp1 y`. Establish `hpint : ∀ j, Integrable (fun y => (p y : ℂ) * term n s (e j) y)` using `fun j => (hint j).bdd_mul hpm hpb`. Establish `hFint : ∀ j, Integrable (F j)` using `fun j => (hpint j).const_mul (a j)`. Establish `hnorm : ∀ j y, ‖F j y‖ = ‖a j‖ * (p y * ‖term n s (e j) y‖)`. Introduce `j y`.

Simplify using `only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]`. Establish `hFsum : Summable fun j => ∫ y, ‖F j y‖`. Establish `hi : ∀ j, ∫ y, ‖F j y‖ = ‖a j‖ * ∫ y, p y * ‖term n s (e j) y‖`. Introduce `j`. Repeatedly rewrite using `[hnorm]`.

Conclude with `integral_const_mul _ _`. Use `Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) (fun j => ?_) (hsum.mul_left C)` and prove the remaining obligations. Rewrite using `[hi]`. Conclude with `mul_le_mul_of_nonneg_right (hC j) (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))`. Establish `h` using `hasSum_integral_of_summable_integral_norm hFint hFsum`.

Establish `hl : (fun j => ∫ y, F j y) = fun j => a j * ∫ y, (p y : ℂ) * term n s (e j) y`. Use function extensionality and compare the values at `j`. Conclude with `integral_const_mul _ _`. Establish `hr : (fun y => ∑' j, F j y) = fun y => (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))`. Use function extensionality and compare the values at `y`.

Simplify using `only [hF, GlobalTheory.HeckeTheta.theta, term]`. Rewrite using `[← tsum_mul_left, ← tsum_mul_right]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[hl, hr]`. Conclude with `h`.
-/
theorem hasSum_integral_theta (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ)
    (hC : ∀ j, ‖a j‖ ≤ C) (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∀ y, p y ≤ 1) (hint : ∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j)))
    (hsum : Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖)) :
    HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y)
      (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  set F : ι → (I → ℝ) → ℂ := fun j y => a j * ((p y : ℂ) * term n s (e j) y) with hF
  have hpm : AEStronglyMeasurable (fun y => (p y : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hp).aestronglyMeasurable
  have hpb : ∀ᵐ y ∂(volume : Measure (I → ℝ)), ‖(p y : ℂ)‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]; exact hp1 y
  have hpint : ∀ j, Integrable (fun y => (p y : ℂ) * term n s (e j) y) :=
    fun j => (hint j).bdd_mul hpm hpb
  have hFint : ∀ j, Integrable (F j) := fun j => (hpint j).const_mul (a j)
  have hnorm : ∀ j y, ‖F j y‖ = ‖a j‖ * (p y * ‖term n s (e j) y‖) := by
    intro j y
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]
  have hFsum : Summable fun j => ∫ y, ‖F j y‖ := by
    have hi : ∀ j, ∫ y, ‖F j y‖ = ‖a j‖ * ∫ y, p y * ‖term n s (e j) y‖ := by
      intro j; simp_rw [hnorm]; exact integral_const_mul _ _
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) (fun j => ?_) (hsum.mul_left C)
    rw [hi]
    exact mul_le_mul_of_nonneg_right (hC j)
      (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))
  have h := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hl : (fun j => ∫ y, F j y) = fun j => a j * ∫ y, (p y : ℂ) * term n s (e j) y := by
    funext j; exact integral_const_mul _ _
  have hr : (fun y => ∑' j, F j y) =
      fun y => (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
    funext y
    simp only [hF, GlobalTheory.HeckeTheta.theta, term]
    rw [← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext j; ring
  rw [hl, hr] at h
  exact h

end GlobalTheory.HeckeMellin
