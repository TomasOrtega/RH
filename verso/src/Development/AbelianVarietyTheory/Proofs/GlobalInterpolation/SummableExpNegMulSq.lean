import Mathlib

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ShiftedTheta

/- English proof (translation)
Establish `h` using `HasSum.of_nat_of_neg (f := fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two) (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)`. Establish `e : Real.pi ^ 2 / 6 + Real.pi ^ 2 / 6 - 1 / ((0 : ℤ) : ℝ) ^ 2 = Real.pi ^ 2 / 3`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Conclude with `e ▸ h`.
-/
theorem hasSum_int_inv_sq :
    HasSum (fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by
  have h := HasSum.of_nat_of_neg (f := fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
  have e : Real.pi ^ 2 / 6 + Real.pi ^ 2 / 6 - 1 / ((0 : ℤ) : ℝ) ^ 2 = Real.pi ^ 2 / 3 := by
    simp
    ring
  exact e ▸ h

/- English proof (translation)
Establish `h` using `Real.pow_div_factorial_le_exp y hy.le 2`. Rewrite using `[Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]`. Evaluate the numerical expressions using `[Nat.factorial] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_neg_le {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 2
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  norm_num [Nat.factorial] at h
  linarith

/- English proof (translation)
Establish `h0 : (n : ℝ) ≠ 0` using `by exact_mod_cast hn`. Establish `h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2`. Establish `: (1 : ℤ) ≤ n ^ 2`. Use `sq_pos_of_ne_zero hn` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `this` after adjusting the coercions. Use `(exp_neg_le (by positivity)).trans ?_` and prove the remaining obligations. Rewrite using `[div_mul_div_comm, mul_one, mul_pow]`. Use `div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)` and prove the remaining obligations.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-(c * (n : ℝ) ^ 2)) ≤ 2 / c ^ 2 * (1 / (n : ℝ) ^ 2) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have := sq_pos_of_ne_zero hn
      omega
    exact_mod_cast this
  refine (exp_neg_le (by positivity)).trans ?_
  rw [div_mul_div_comm, mul_one, mul_pow]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  nlinarith

/- English proof (translation)
Use `Summable.of_norm_bounded_eventually (hasSum_int_inv_sq.summable.mul_left (2 / c ^ 2)) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn`. Rewrite using `[Real.norm_of_nonneg (Real.exp_pos _).le]`. Conclude with `exp_neg_mul_sq_le hc hn`.
-/
theorem summable_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually (hasSum_int_inv_sq.summable.mul_left (2 / c ^ 2)) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_mul_sq_le hc hn

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_) ((summable_exp_neg_mul_sq (half_pos hs)).mul_left (Real.exp (s * θ ^ 2)))` and prove the remaining obligations. Rewrite using `[← Real.exp_add, Real.exp_le_exp]`. Use polynomial arithmetic with `[mul_nonneg hs.le (sq_nonneg ((m : ℝ) + 2 * θ))]`.
-/
theorem summable_shifted {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    Summable fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
    ((summable_exp_neg_mul_sq (half_pos hs)).mul_left (Real.exp (s * θ ^ 2)))
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hs.le (sq_nonneg ((m : ℝ) + 2 * θ))]

/- English proof (translation)
Establish `ha : 0 < Real.pi / s` using `div_pos Real.pi_pos hs`. Rewrite using `[Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re])]`. Establish `h1 : ((Real.pi / s : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / s) : ℂ)`. Rewrite using `[Real.sqrt_eq_rpow, ofReal_cpow ha.le]`. Evaluate the numerical expressions.

Establish `h2 : (Real.sqrt (Real.pi / s) : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.2 ha).ne'` after adjusting the coercions. Rewrite using `[h1, ← mul_assoc, mul_one_div_cancel h2, one_mul, ofReal_tsum]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Establish `h3 : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Establish `h4 : (s : ℂ) ≠ 0` using `by exact_mod_cast hs.ne'`. Establish `h5 : I * (-I * θ) = θ`. Rewrite using `[← mul_assoc, mul_neg, I_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h5]`.

Use `push_cast`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem poisson {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    ((∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) : ℝ) : ℂ) =
      (Real.sqrt (Real.pi / s) : ℂ) * ∑' n : ℤ,
        cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) := by
  have ha : 0 < Real.pi / s := div_pos Real.pi_pos hs
  rw [Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re])]
  have h1 : ((Real.pi / s : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / s) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow ha.le]
    norm_num
  have h2 : (Real.sqrt (Real.pi / s) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  rw [h1, ← mul_assoc, mul_one_div_cancel h2, one_mul, ofReal_tsum]
  refine tsum_congr fun n => ?_
  have h3 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h5 : I * (-I * θ) = θ := by
    rw [← mul_assoc, mul_neg, I_mul_I]; ring
  rw [h5]
  push_cast
  congr 1
  field_simp

/- English proof (translation)
Introduce `s θ hs`. Use `⟨summable_shifted θ hs, ?_⟩` and prove the remaining obligations. Use `set g : ℤ → ℂ := fun n => cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) with hg`. Establish `hpi` using `Real.pi_pos`. Establish `hc : 0 < Real.pi ^ 2 / s` using `by positivity`.

Establish `hn : ∀ n : ℤ, ‖g n‖ = Real.exp (-(Real.pi ^ 2 / s * (n : ℝ) ^ 2))`. Introduce `n`. Establish `e : -(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n = ((-(Real.pi ^ 2 / s * (n : ℝ) ^ 2) : ℝ) : ℂ) + ((-(2 * Real.pi * θ * n) : ℝ) : ℂ) * I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hg]`. Rewrite using `[e, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp_ofReal]`. Establish `hsum : Summable g` using `Summable.of_norm_bounded (summable_exp_neg_mul_sq hc) fun n => (hn n).le`. Establish `hb : ‖∑' n : ℤ, if n = 0 then 0 else g n‖ ≤ 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3)`. Use `tsum_of_norm_bounded (hasSum_int_inv_sq.mul_left _) fun n => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Rewrite using `[norm_zero]`. Check the signs of the components of the expression. Rewrite using `[hn]`. Conclude with `exp_neg_mul_sq_le hc h`.

Establish `hb2 : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) ≤ s ^ 2`. Establish `e : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) = s ^ 2 * (2 / (3 * Real.pi ^ 2))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Use `mul_le_of_le_one_right (sq_nonneg _) ?_` and prove the remaining obligations.

Rewrite using `[div_le_one (by positivity)]`. Use polynomial arithmetic with `[Real.pi_gt_three]`. Establish `hg0 : g 0 = 1` using `by simp [hg]`. Establish `hp` using `poisson θ hs`. Express the relevant statement in the definitionally equal form `_ = _ * ∑' n, g n at hp`.

Rewrite `hp` using `[hsum.tsum_eq_add_tsum_ite 0, hg0]`. Rewrite using `[← Real.norm_eq_abs, ← Complex.norm_real, ofReal_sub, hp, mul_add, mul_one, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]`. Conclude with `mul_le_mul_of_nonneg_left (hb.trans hb2) (Real.sqrt_nonneg _)`.
-/
theorem shifted_theta_bound : ∀ s θ : ℝ, 0 < s → Summable (fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2))) ∧ |∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) - Real.sqrt (Real.pi / s)| ≤ Real.sqrt (Real.pi / s) * s ^ 2 := by
  intro s θ hs
  refine ⟨summable_shifted θ hs, ?_⟩
  set g : ℤ → ℂ := fun n =>
    cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) with hg
  have hpi := Real.pi_pos
  have hc : 0 < Real.pi ^ 2 / s := by positivity
  have hn : ∀ n : ℤ, ‖g n‖ = Real.exp (-(Real.pi ^ 2 / s * (n : ℝ) ^ 2)) := by
    intro n
    have e : -(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n
        = ((-(Real.pi ^ 2 / s * (n : ℝ) ^ 2) : ℝ) : ℂ) + ((-(2 * Real.pi * θ * n) : ℝ) : ℂ) * I := by
      push_cast
      ring
    simp only [hg]
    rw [e, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_exp_ofReal]
  have hsum : Summable g :=
    Summable.of_norm_bounded (summable_exp_neg_mul_sq hc) fun n => (hn n).le
  have hb : ‖∑' n : ℤ, if n = 0 then 0 else g n‖ ≤ 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) := by
    refine tsum_of_norm_bounded (hasSum_int_inv_sq.mul_left _) fun n => ?_
    split_ifs with h
    · rw [norm_zero]; positivity
    · rw [hn]; exact exp_neg_mul_sq_le hc h
  have hb2 : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) ≤ s ^ 2 := by
    have e : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) = s ^ 2 * (2 / (3 * Real.pi ^ 2)) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hg0 : g 0 = 1 := by simp [hg]
  have hp := poisson θ hs
  change _ = _ * ∑' n, g n at hp
  rw [hsum.tsum_eq_add_tsum_ite 0, hg0] at hp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ofReal_sub, hp, mul_add, mul_one,
    add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hb.trans hb2) (Real.sqrt_nonneg _)

end GlobalTheory.ShiftedTheta
