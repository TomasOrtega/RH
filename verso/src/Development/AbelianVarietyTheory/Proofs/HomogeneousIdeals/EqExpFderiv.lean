import Mathlib

universe u_1

namespace GlobalTheory.ExpOfFrechetDerivative

/- English proof (translation)
Use `set L := fderiv ℂ f (0 : E) with hL`. Establish `hf0 : f 0 = 1`. Establish `h00` using `hmul 0 0`. Rewrite `h00` using `[add_zero]`. Establish `hfac : f 0 * (f 0 - 1) = 0` using `by rw [mul_sub, mul_one, ← h00, sub_self]`.

Break down `mul_eq_zero.mp hfac with h | h` into its components or cases. Conclude with `absurd h h0`. Conclude with `sub_eq_zero.mp h`. Establish `hD : ∀ x : E, HasFDerivAt f (f x • L) x`. Introduce `x`.

Establish `h1 : HasFDerivAt f L (x - x)`. Rewrite using `[sub_self]`. Conclude with `hd.hasFDerivAt`. Establish `h2 : HasFDerivAt (fun y : E => f (y - x)) L x`. Establish `h` using `h1.comp (f := fun y : E => y - x) x ((hasFDerivAt_id x).sub_const x)`.

Rewrite `h` using `[ContinuousLinearMap.comp_id]`. Conclude with `h`. Use `(h2.const_mul (f x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show f y = f x * f (y - x)`. Rewrite using `[← hmul, add_sub_cancel]`.

Establish `hE : ∀ y : E, HasFDerivAt (fun y => f y * Complex.exp (-(L y))) (f y • (Complex.exp (-(L y)) • -L) + Complex.exp (-(L y)) • (f y • L)) y` using `fun y => (hD y).mul (L.hasFDerivAt.neg.cexp)`. Establish `hzero : ∀ y, fderiv ℂ (fun y => f y * Complex.exp (-(L y))) y = 0`. Introduce `y`. Rewrite using `[(hE y).fderiv]`. Use extensionality with `v`.

Simplify using `only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `is_const_of_fderiv_eq_zero (fun y => (hE y).differentiableAt) hzero z 0`. Simplify using `only [map_zero, neg_zero, Complex.exp_zero, mul_one, hf0] at hc`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`. Use `_ = Complex.exp (L z) := by rw [hc, one_mul]`.
-/
theorem eq_exp_fderiv {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    (hd : DifferentiableAt ℂ f (0 : E)) (h0 : f (0 : E) ≠ (0 : ℂ))
    (hmul : ∀ x y : E, f (x + y) = f x * f y) (z : E) :
    f z = Complex.exp ((fderiv ℂ f (0 : E) : E → ℂ) z) := by
  set L := fderiv ℂ f (0 : E) with hL

  have hf0 : f 0 = 1 := by
    have h00 := hmul 0 0
    rw [add_zero] at h00
    have hfac : f 0 * (f 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h00, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h

  have hD : ∀ x : E, HasFDerivAt f (f x • L) x := by
    intro x
    have h1 : HasFDerivAt f L (x - x) := by
      rw [sub_self]
      exact hd.hasFDerivAt
    have h2 : HasFDerivAt (fun y : E => f (y - x)) L x := by
      have h := h1.comp (f := fun y : E => y - x) x ((hasFDerivAt_id x).sub_const x)
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    refine (h2.const_mul (f x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    show f y = f x * f (y - x)
    rw [← hmul, add_sub_cancel]

  have hE : ∀ y : E, HasFDerivAt (fun y => f y * Complex.exp (-(L y)))
      (f y • (Complex.exp (-(L y)) • -L) + Complex.exp (-(L y)) • (f y • L)) y :=
    fun y => (hD y).mul (L.hasFDerivAt.neg.cexp)
  have hzero : ∀ y, fderiv ℂ (fun y => f y * Complex.exp (-(L y))) y = 0 := by
    intro y
    rw [(hE y).fderiv]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hc := is_const_of_fderiv_eq_zero (fun y => (hE y).differentiableAt) hzero z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one, hf0] at hc
  calc f z = f z * Complex.exp (-(L z)) * Complex.exp (L z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (L z) := by rw [hc, one_mul]

end GlobalTheory.ExpOfFrechetDerivative
