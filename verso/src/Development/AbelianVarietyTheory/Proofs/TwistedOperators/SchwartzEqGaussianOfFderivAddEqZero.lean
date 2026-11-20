import Mathlib
open scoped SchwartzMap

namespace GlobalTheory

/- English proof (translation)
Establish `hE : ∀ y : EuclideanSpace ℝ l, HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2)) (Real.exp (Real.pi * ‖y‖ ^ 2) • (Real.pi • (2 • innerSL ℝ y))) y`. Introduce `y`. Conclude with `((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul Real.pi).exp`. Establish `hu : ∀ y : EuclideanSpace ℝ l, HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y) (0 : EuclideanSpace ℝ l →L[ℝ] ℂ) y`. Introduce `y`.

Establish `h1` using `(hE y).smul (h.differentiableAt (x := y)).hasFDerivAt`. Use `h1.congr_fderiv ?_` and prove the remaining obligations. Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Apply `(EuclideanSpace.basisFun l ℝ).toBasis.ext` to reduce the goal to its premises. Introduce `j`.

Establish `h2` using `H j y`. Establish `h3 : fderiv ℝ (⇑h) y (EuclideanSpace.single j 1) = -(2 * Real.pi * (y j : ℂ) * h y)` using `eq_neg_of_add_eq_zero_left h2`. Simplify using `[h3, EuclideanSpace.inner_single_right]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f := fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y) (fun y => (hu y).differentiableAt) (fun y => (hu y).fderiv) x 0`.

Simplify using `only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero, one_smul] at hc`. Rewrite using `[← hc, Complex.real_smul, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]`. Simplify using the standard rewrite rules.
-/
theorem schwartz_eq_gaussian_of_fderiv_add_eq_zero
    (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ))
    (H : ∀ (j : l) (x : EuclideanSpace ℝ l),
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0)
    (x : EuclideanSpace ℝ l) :
    h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  have hE : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2))
        (Real.exp (Real.pi * ‖y‖ ^ 2) • (Real.pi • (2 • innerSL ℝ y))) y := by
    intro y
    exact ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul Real.pi).exp
  have hu : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
        (0 : EuclideanSpace ℝ l →L[ℝ] ℂ) y := by
    intro y
    have h1 := (hE y).smul (h.differentiableAt (x := y)).hasFDerivAt
    refine h1.congr_fderiv ?_
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun l ℝ).toBasis.ext
    intro j
    have h2 := H j y
    have h3 : fderiv ℝ (⇑h) y (EuclideanSpace.single j 1) = -(2 * Real.pi * (y j : ℂ) * h y) :=
      eq_neg_of_add_eq_zero_left h2
    simp [h3, EuclideanSpace.inner_single_right]
    ring
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (f := fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
    (fun y => (hu y).differentiableAt) (fun y => (hu y).fderiv) x 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, one_smul] at hc
  rw [← hc, Complex.real_smul, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

end GlobalTheory
