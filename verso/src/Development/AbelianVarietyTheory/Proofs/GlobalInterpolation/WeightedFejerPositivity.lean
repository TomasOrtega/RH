import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `hre : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), w ^ j).re = 1 + ∑ j ∈ Finset.Icc 1 n, (w ^ j).re`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Finset.sum_range_succ, Complex.add_re, ih, Finset.sum_Icc_succ_top (by omega)]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `J with`. Consider the case `zero => simp`. Consider the case `succ J ih`.

Establish `h1 : ∑ j ∈ Finset.range (J + 1 + 1), w ^ j = w * (∑ j ∈ Finset.range (J + 1), w ^ j) + 1`. Rewrite using `[Finset.sum_range_succ', Finset.mul_sum]`. Simplify using `[pow_succ']`. Establish `h2 : ∑ j ∈ Finset.Icc 1 (J + 1), (((J + 1 : ℕ) : ℝ) + 1 - j) * (w ^ j).re = ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re + ∑ j ∈ Finset.Icc 1 (J + 1), (w ^ j).re`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← Finset.sum_add_distrib]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_ push_cast` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3` using `hre (J + 1)`. Establish `hw2 : Complex.normSq w ≤ 1`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use `norm_nonneg w` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[h2]`. Use `set S := ∑ j ∈ Finset.range (J + 1), w ^ j`. Rewrite `h3`, the goal using `[h1]`. Establish `h4 : Complex.normSq (w * S + 1) = Complex.normSq w * Complex.normSq S + 2 * (w * S + 1).re - 1`. Rewrite using `[Complex.normSq_add, map_mul]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `Complex.normSq_nonneg S`. Rewrite using `[h4, h3]`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem normSq_geomSum_le_fejer (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    Complex.normSq (∑ j ∈ Finset.range (J + 1), w ^ j) ≤
      (J + 1 : ℝ) + 2 * ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re := by
  have hre : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), w ^ j).re
      = 1 + ∑ j ∈ Finset.Icc 1 n, (w ^ j).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Complex.add_re, ih, Finset.sum_Icc_succ_top (by omega)]
      ring
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 : ∑ j ∈ Finset.range (J + 1 + 1), w ^ j
        = w * (∑ j ∈ Finset.range (J + 1), w ^ j) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ']
    have h2 : ∑ j ∈ Finset.Icc 1 (J + 1), (((J + 1 : ℕ) : ℝ) + 1 - j) * (w ^ j).re
        = ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re
          + ∑ j ∈ Finset.Icc 1 (J + 1), (w ^ j).re := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      · push_cast; ring
    have h3 := hre (J + 1)
    have hw2 : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg w
      nlinarith
    rw [h2]
    set S := ∑ j ∈ Finset.range (J + 1), w ^ j
    rw [h1] at h3 ⊢
    have h4 : Complex.normSq (w * S + 1) = Complex.normSq w * Complex.normSq S
        + 2 * (w * S + 1).re - 1 := by
      rw [Complex.normSq_add, map_mul]
      simp
      ring
    have h5 := Complex.normSq_nonneg S
    rw [h4, h3]
    push_cast
    nlinarith

/- English proof (translation)
Establish `h` using `normSq_geomSum_le_fejer w hw J`. Establish `h0` using `Complex.normSq_nonneg (∑ j ∈ Finset.range (J + 1), w ^ j)`. Establish `hJ : (0 : ℝ) < J + 1` using `by positivity`. Establish `h1 : ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re = (∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re) / (J + 1)`. Rewrite using `[Finset.sum_div]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1, le_div_iff₀ hJ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fejer_re_ge (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    -(1 / 2) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re := by
  have h := normSq_geomSum_le_fejer w hw J
  have h0 := Complex.normSq_nonneg (∑ j ∈ Finset.range (J + 1), w ^ j)
  have hJ : (0 : ℝ) < J + 1 := by positivity
  have h1 : ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
      = (∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re) / (J + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [h1, le_div_iff₀ hJ]
  linarith

/- English proof (translation)
Establish `h : ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 n, (j : ℝ) = n * (n + 1) / 2`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Finset.sum_Icc_succ_top (by omega), ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hJ : (0 : ℝ) < J + 1` using `by positivity`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.sum_div, h]`.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_fejer_weights (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) = (J : ℝ) / 2 := by
  have h : ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 n, (j : ℝ) = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast; ring
  have hJ : (0 : ℝ) < J + 1 := by positivity
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, h]
  simp
  field_simp
  ring

/- English proof (translation)
Rewrite using `[Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e1 : Complex.exp (θ * I) ^ j = Complex.exp (((j * θ : ℝ) : ℂ) * I)`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Complex.exp (-(θ * I)) ^ j = Complex.exp (((-(j * θ) : ℝ) : ℂ) * I)`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_pow, mul_pow, e1, e2, Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weighted_fejer_split (J : ℕ) (θ : ℝ) (w : ℂ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re
      = ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (θ * I)) ^ j).re) / 2
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (-(θ * I))) ^ j).re) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : Complex.exp (θ * I) ^ j = Complex.exp (((j * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(θ * I)) ^ j = Complex.exp (((-(j * θ) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, mul_pow, e1, e2, Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ring

/- English proof (translation)
Introduce `J θ`. Establish `n1 : ‖Complex.exp (θ * I)‖ = 1` using `Complex.norm_exp_ofReal_mul_I θ`. Establish `n2 : ‖Complex.exp (-(θ * I))‖ = 1`. Rewrite using `[Complex.exp_neg, norm_inv, n1, inv_one]`. Use `⟨fun w hw => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[weighted_fejer_split]`. Establish `a` using `fejer_re_ge w hw J`. Establish `b` using `fejer_re_ge (w * Complex.exp (θ * I)) (by rw [norm_mul, n1, mul_one]; exact hw) J`. Establish `c` using `fejer_re_ge (w * Complex.exp (-(θ * I))) (by rw [norm_mul, n2, mul_one]; exact hw) J`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[weighted_fejer_split]`. Establish `a` using `fejer_re_ge (Complex.exp (θ * I)) n1.le J`. Establish `b` using `fejer_re_ge (Complex.exp (θ * I) * Complex.exp (θ * I)) (by rw [norm_mul, n1, mul_one]) J`. Establish `c : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1`. Rewrite using `[← Complex.exp_add]`.

Simplify using the standard rewrite rules. Rewrite using `[c]`. Simplify using `only [one_pow, Complex.one_re, mul_one]`. Rewrite using `[sum_fejer_weights]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weighted_fejer_positivity : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  intro J θ
  have n1 : ‖Complex.exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have n2 : ‖Complex.exp (-(θ * I))‖ = 1 := by
    rw [Complex.exp_neg, norm_inv, n1, inv_one]
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [weighted_fejer_split]
    have a := fejer_re_ge w hw J
    have b := fejer_re_ge (w * Complex.exp (θ * I)) (by rw [norm_mul, n1, mul_one]; exact hw) J
    have c := fejer_re_ge (w * Complex.exp (-(θ * I)))
      (by rw [norm_mul, n2, mul_one]; exact hw) J
    linarith
  · rw [weighted_fejer_split]
    have a := fejer_re_ge (Complex.exp (θ * I)) n1.le J
    have b := fejer_re_ge (Complex.exp (θ * I) * Complex.exp (θ * I))
      (by rw [norm_mul, n1, mul_one]) J
    have c : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [c]
    simp only [one_pow, Complex.one_re, mul_one]
    rw [sum_fejer_weights]
    linarith

end GlobalTheory
