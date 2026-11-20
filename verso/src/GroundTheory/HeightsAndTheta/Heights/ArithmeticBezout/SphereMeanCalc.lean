import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

def polyP (m : ℕ) (s : ℝ) : ℝ := ∑ j ∈ Finset.range (m + 1), (1 - s) ^ j / (m + 1)

def polyR (m : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (1 - (1 - s) ^ (j + 1)) / ((j + 1) * (m + 1))

def primG (m : ℕ) (s : ℝ) : ℝ := (1 - (1 - s) ^ (m + 1)) / (m + 1) * log s - polyR m s

/- English proof (translation)
Establish `h` using `geom_sum_mul (1 - s) (m + 1)`. Establish `hm : (m : ℝ) + 1 ≠ 0` using `by positivity`. Unfold `polyP`. Rewrite using `[← Finset.sum_div, eq_div_iff hm, mul_div_assoc', div_mul_cancel₀ _ hm]`. Take the linear combination `(-1 : ℝ) * h`.
-/
theorem mul_polyP (m : ℕ) (s : ℝ) : s * polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) := by
  have h := geom_sum_mul (1 - s) (m + 1)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold polyP
  rw [← Finset.sum_div, eq_div_iff hm, mul_div_assoc', div_mul_cancel₀ _ hm]
  linear_combination (-1 : ℝ) * h

/- English proof (translation)
Use `(hasDerivAt_pow k (1 - s)).comp s ((hasDerivAt_id s).const_sub 1)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.
-/
theorem hasDerivAt_one_sub_pow (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - s) ^ k) (-((k : ℝ) * (1 - s) ^ (k - 1))) s := by
  have := (hasDerivAt_pow k (1 - s)).comp s ((hasDerivAt_id s).const_sub 1)
  simpa [Function.comp_def] using this

/- English proof (translation)
Unfold `polyR polyP`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `j _`. Establish `h2` using `((hasDerivAt_one_sub_pow (j + 1) s).const_sub 1).div_const (((j : ℝ) + 1) * (m + 1))`. Use `h2.congr_deriv ?_` and prove the remaining obligations.

Establish `hj : (j : ℝ) + 1 ≠ 0` using `by positivity`. Establish `hm : (m : ℝ) + 1 ≠ 0` using `by positivity`. Rewrite using `[Nat.add_sub_cancel, neg_neg]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasDerivAt_polyR (m : ℕ) (s : ℝ) : HasDerivAt (polyR m) (polyP m s) s := by
  unfold polyR polyP
  apply HasDerivAt.fun_sum
  intro j _
  have h2 := ((hasDerivAt_one_sub_pow (j + 1) s).const_sub 1).div_const (((j : ℝ) + 1) * (m + 1))
  refine h2.congr_deriv ?_
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.add_sub_cancel, neg_neg]
  push_cast
  field_simp

/- English proof (translation)
Rewrite using `[primG, ← mul_polyP]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem primG_eq (m : ℕ) (s : ℝ) : primG m s = polyP m s * (s * log s) - polyR m s := by
  rw [primG, ← mul_polyP]
  ring

/- English proof (translation)
Unfold `polyP`. Use `fun_prop`.
-/
theorem continuous_polyP (m : ℕ) : Continuous (polyP m) := by
  unfold polyP
  fun_prop

/- English proof (translation)
Unfold `polyR`. Use `fun_prop`.
-/
theorem continuous_polyR (m : ℕ) : Continuous (polyR m) := by
  unfold polyR
  fun_prop

/- English proof (translation)
Establish `: primG m = fun s => polyP m s * (s * log s) - polyR m s` using `funext (primG_eq m)`. Rewrite using `[this]`. Conclude with `((continuous_polyP m).mul continuous_mul_log).sub (continuous_polyR m)`.
-/
theorem continuous_primG (m : ℕ) : Continuous (primG m) := by
  have : primG m = fun s => polyP m s * (s * log s) - polyR m s := funext (primG_eq m)
  rw [this]
  exact ((continuous_polyP m).mul continuous_mul_log).sub (continuous_polyR m)

/- English proof (translation)
Establish `hm : (m : ℝ) + 1 ≠ 0` using `by positivity`. Establish `h1 : HasDerivAt (fun s : ℝ => (1 - (1 - s) ^ (m + 1)) / (m + 1)) ((1 - s) ^ m) s`. Use `((hasDerivAt_one_sub_pow (m + 1) s).const_sub 1).div_const ((m : ℝ) + 1)` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel, neg_neg]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `h2` using `(h1.mul (hasDerivAt_log hs.ne')).sub (hasDerivAt_polyR m s)`. Establish `h3 : HasDerivAt (primG m) ((1 - s) ^ m * log s + (1 - (1 - s) ^ (m + 1)) / (↑m + 1) * s⁻¹ - polyP m s) s` using `h2`. Use `h3.congr_deriv ?_` and prove the remaining obligations.

Use `mul_polyP m s` as an intermediate fact. Establish `hP : polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) * s⁻¹`. Rewrite using `[← this]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hP]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_primG (m : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (primG m) ((1 - s) ^ m * log s) s := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => (1 - (1 - s) ^ (m + 1)) / (m + 1)) ((1 - s) ^ m) s := by
    have := ((hasDerivAt_one_sub_pow (m + 1) s).const_sub 1).div_const ((m : ℝ) + 1)
    refine this.congr_deriv ?_
    rw [Nat.add_sub_cancel, neg_neg]
    push_cast
    field_simp
  have h2 := (h1.mul (hasDerivAt_log hs.ne')).sub (hasDerivAt_polyR m s)
  have h3 : HasDerivAt (primG m)
      ((1 - s) ^ m * log s + (1 - (1 - s) ^ (m + 1)) / (↑m + 1) * s⁻¹ - polyP m s) s := h2
  refine h3.congr_deriv ?_
  have := mul_polyP m s
  have hP : polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) * s⁻¹ := by
    rw [← this]; field_simp
  rw [hP]
  ring

/- English proof (translation)
Simplify using `[primG, polyR]`.
-/
theorem primG_zero (m : ℕ) : primG m 0 = 0 := by
  simp [primG, polyR]

/- English proof (translation)
Simplify using `only [primG, polyR, sub_self, log_one, mul_zero, zero_sub, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]`. Rewrite using `[harmonic]`. Use `push_cast`. Rewrite using `[neg_div, Finset.sum_div]`. Use `congr 1`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Clear the denominators using the available nonvanishing facts.
-/
theorem primG_one (m : ℕ) : primG m 1 = -(harmonic (m + 1) : ℝ) / (m + 1) := by
  simp only [primG, polyR, sub_self, log_one, mul_zero, zero_sub, ne_eq, add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  rw [harmonic]
  push_cast
  rw [neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp

/- English proof (translation)
Establish `hm : (m : ℝ) + 1 ≠ 0` using `by positivity`. Establish `hd : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1))) (y * (1 - y ^ 2) ^ m) y`. Introduce `y _`. Establish `hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y` using `by simpa using hasDerivAt_pow 2 y`. Use `(HasDerivAt.comp (h := fun x : ℝ => x ^ 2) y (hasDerivAt_one_sub_pow (m + 1) (y ^ 2)) hp).neg.div_const (2 * ((m : ℝ) + 1))` as an intermediate fact.

Establish `h3 : HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1))) (-(-((((m + 1 : ℕ) : ℝ)) * (1 - y ^ 2) ^ (m + 1 - 1)) * (2 * y)) / (2 * ((m : ℝ) + 1))) y` using `this`. Use `h3.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := fun y => y * (1 - y ^ 2) ^ m) hd (Continuous.intervalIntegrable (by fun_prop) 0 1)]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.
-/
theorem integral_disc_weight (m : ℕ) :
    ∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ m = 1 / (2 * ((m : ℝ) + 1)) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1)))
      (y * (1 - y ^ 2) ^ m) y := by
    intro y _
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have := (HasDerivAt.comp (h := fun x : ℝ => x ^ 2) y (hasDerivAt_one_sub_pow (m + 1) (y ^ 2))
      hp).neg.div_const (2 * ((m : ℝ) + 1))
    have h3 : HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1)))
        (-(-((((m + 1 : ℕ) : ℝ)) * (1 - y ^ 2) ^ (m + 1 - 1)) * (2 * y)) / (2 * ((m : ℝ) + 1))) y :=
      this
    refine h3.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := fun y => y * (1 - y ^ 2) ^ m) hd
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  field_simp
  simp

/- English proof (translation)
Establish `hm : (m : ℝ) + 1 ≠ 0` using `by positivity`. Establish `hc : ContinuousOn (fun y : ℝ => primG m (y ^ 2) / 4) (Icc 0 1)` using `((continuous_primG m).comp (continuous_pow 2)).div_const 4 |>.continuousOn`. Establish `hd : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y : ℝ => primG m (y ^ 2) / 4) (y * log y * (1 - y ^ 2) ^ m) y`. Introduce `y hy`. Establish `hy2 : 0 < y ^ 2` using `pow_pos hy.1 2`.

Establish `hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y` using `by simpa using hasDerivAt_pow 2 y`. Use `(HasDerivAt.comp (h := fun x : ℝ => x ^ 2) y (hasDerivAt_primG m hy2) hp).div_const 4` as an intermediate fact. Establish `h3 : HasDerivAt (fun y : ℝ => primG m (y ^ 2) / 4) ((1 - y ^ 2) ^ m * log (y ^ 2) * (2 * y) / 4) y` using `this`. Use `h3.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hi : IntervalIntegrable (fun y : ℝ => y * log y * (1 - y ^ 2) ^ m) volume 0 1`. Apply `Continuous.intervalIntegrable` to reduce the goal to its premises. Conclude with `continuous_mul_log.mul (by fun_prop)`.

Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]`. Simplify using `only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, primG_one, primG_zero, zero_div, sub_zero]`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_disc_log_weight (m : ℕ) :
    ∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m = -(harmonic (m + 1) : ℝ) / (4 * (m + 1)) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hc : ContinuousOn (fun y : ℝ => primG m (y ^ 2) / 4) (Icc 0 1) :=
    ((continuous_primG m).comp (continuous_pow 2)).div_const 4 |>.continuousOn
  have hd : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y : ℝ => primG m (y ^ 2) / 4)
      (y * log y * (1 - y ^ 2) ^ m) y := by
    intro y hy
    have hy2 : 0 < y ^ 2 := pow_pos hy.1 2
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have := (HasDerivAt.comp (h := fun x : ℝ => x ^ 2) y (hasDerivAt_primG m hy2) hp).div_const 4
    have h3 : HasDerivAt (fun y : ℝ => primG m (y ^ 2) / 4)
        ((1 - y ^ 2) ^ m * log (y ^ 2) * (2 * y) / 4) y := this
    refine h3.congr_deriv ?_
    rw [log_pow]
    push_cast
    ring
  have hi : IntervalIntegrable (fun y : ℝ => y * log y * (1 - y ^ 2) ^ m) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_mul_log.mul (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]
  simp only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, primG_one,
    primG_zero, zero_div, sub_zero]
  field_simp

end SphereMean

end

end GroundTheory.Heights₂.Heights
