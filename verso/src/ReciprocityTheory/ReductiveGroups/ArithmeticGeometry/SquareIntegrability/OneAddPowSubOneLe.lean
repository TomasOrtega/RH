import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

/- English proof (translation)
Establish `hβ : ∀ i, 0 ≤ β i` using `fun i => (norm_nonneg _).trans (hy i)`. Establish `hδ : ∀ i, 0 ≤ δ i` using `fun i => (norm_nonneg _).trans (hxy i)`. Establish `hx : ∀ i, ‖x i‖ ≤ β i + δ i` using `fun i => by`. Combine the equalities or inequalities in the displayed calculation. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]`. Establish `hX : ‖∏ i ∈ s, x i‖ ≤ ∏ i ∈ s, (β i + δ i)`. Rewrite using `[norm_prod]`.

Conclude with `Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx i)`. Establish `hP : ∏ i ∈ s, β i ≤ ∏ i ∈ s, (β i + δ i)` using `Finset.prod_le_prod (fun i _ => hβ i) (fun i _ => le_add_of_nonneg_right (hδ i))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_mul]`. Use `_ ≤ δ a * ∏ i ∈ s, (β i + δ i) + β a * (∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i) := by`.

Conclude with `add_le_add (mul_le_mul (hxy a) hX (norm_nonneg _) (hδ a)) (mul_le_mul (hy a) ih (norm_nonneg _) (hβ a))`. Use `_ = (β a + δ a) * ∏ i ∈ s, (β i + δ i) - β a * ∏ i ∈ s, β i := by ring`.
-/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) (β δ : ι → ℝ)
    (hy : ∀ i, ‖y i‖ ≤ β i) (hxy : ∀ i, ‖x i - y i‖ ≤ δ i) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i := by
  classical
  have hβ : ∀ i, 0 ≤ β i := fun i => (norm_nonneg _).trans (hy i)
  have hδ : ∀ i, 0 ≤ δ i := fun i => (norm_nonneg _).trans (hxy i)
  have hx : ∀ i, ‖x i‖ ≤ β i + δ i := fun i => by
    calc ‖x i‖ = ‖y i + (x i - y i)‖ := by ring_nf
      _ ≤ ‖y i‖ + ‖x i - y i‖ := norm_add_le _ _
      _ ≤ β i + δ i := add_le_add (hy i) (hxy i)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have hX : ‖∏ i ∈ s, x i‖ ≤ ∏ i ∈ s, (β i + δ i) := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx i)
    have hP : ∏ i ∈ s, β i ≤ ∏ i ∈ s, (β i + δ i) :=
      Finset.prod_le_prod (fun i _ => hβ i) (fun i _ => le_add_of_nonneg_right (hδ i))
    calc ‖x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i‖
        = ‖(x a - y a) * ∏ i ∈ s, x i + y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := by ring_nf
      _ ≤ ‖(x a - y a) * ∏ i ∈ s, x i‖ + ‖y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := norm_add_le _ _
      _ = ‖x a - y a‖ * ‖∏ i ∈ s, x i‖ + ‖y a‖ * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ δ a * ∏ i ∈ s, (β i + δ i) + β a * (∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i) := by
          exact add_le_add (mul_le_mul (hxy a) hX (norm_nonneg _) (hδ a))
            (mul_le_mul (hy a) ih (norm_nonneg _) (hβ a))
      _ = (β a + δ a) * ∏ i ∈ s, (β i + δ i) - β a * ∏ i ∈ s, β i := by ring

/- English proof (translation)
Rewrite using `[← Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun T _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, norm_mul]`. Establish `h` using `norm_prod_sub_prod_le Finset.univ (D T) (A T) α δ (hA T) (hD T)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hsg T`. Use `_ ≤ _ := by rw [one_mul]; exact h`. Use `_ = Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.
-/
theorem norm_sum_prod_sub_le {τ ι : Type*} [Fintype τ] [Fintype ι] (sg : τ → ℂ)
    (hsg : ∀ T, ‖sg T‖ ≤ 1) (D A : τ → ι → ℂ) (α δ : ι → ℝ) (hA : ∀ T k, ‖A T k‖ ≤ α k)
    (hD : ∀ T k, ‖D T k - A T k‖ ≤ δ k) :
    ‖∑ T, sg T * ∏ k, D T k - ∑ T, sg T * ∏ k, A T k‖ ≤
      Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ T, (sg T * ∏ k, D T k - sg T * ∏ k, A T k)‖
      ≤ ∑ T, ‖sg T * ∏ k, D T k - sg T * ∏ k, A T k‖ := norm_sum_le _ _
    _ ≤ ∑ _T : τ, (∏ k, (α k + δ k) - ∏ k, α k) := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [← mul_sub, norm_mul]
        have h := norm_prod_sub_prod_le Finset.univ (D T) (A T) α δ (hA T) (hD T)
        calc ‖sg T‖ * ‖∏ k, D T k - ∏ k, A T k‖ ≤ 1 * ‖∏ k, D T k - ∏ k, A T k‖ := by
              gcongr
              exact hsg T
          _ ≤ _ := by rw [one_mul]; exact h
    _ = Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h1 : (1 : ℝ) ≤ (1 + x) ^ n`. Establish `h : (1 : ℝ) ^ n ≤ (1 + x) ^ n` using `by gcongr; linarith`.

Simplify using `using h`. Establish `h2 : (1 : ℝ) ≤ (1 + x) ^ n * (1 + x)` using `by nlinarith`. Establish `h3` using `mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + x)`. Use `push_cast`. Rewrite using `[pow_succ]`.

Use polynomial arithmetic with `[mul_nonneg hx (sub_nonneg.2 h2)]`.
-/
theorem one_add_pow_sub_one_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (1 + x) ^ m - 1 ≤ m * x * (1 + x) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ (1 + x) ^ n := by
      have h : (1 : ℝ) ^ n ≤ (1 + x) ^ n := by gcongr; linarith
      simpa using h
    have h2 : (1 : ℝ) ≤ (1 + x) ^ n * (1 + x) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + x)
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg hx (sub_nonneg.2 h2)]

/- English proof (translation)
Establish `hr1 : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hr0 : (0 : ℝ) < r` using `by linarith`. Establish `hlogr : 0 ≤ Real.log r` using `Real.log_nonneg hr1`. Establish `hlog4 : Real.log 4 ≤ 2`. Rewrite using `[Real.log_le_iff_le_exp (by norm_num)]`.

Establish `h1 : (2 : ℝ) ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `h2 : Real.exp 2 = Real.exp 1 * Real.exp 1` using `by rw [← Real.exp_add]; norm_num`. Rewrite using `[h2]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hD0 : (0 : ℝ) ≤ D` using `Nat.cast_nonneg D`.

Establish `h2D : 2 * (D : ℝ) ≤ Real.exp (2 * D)` using `by linarith [Real.add_one_le_exp (2 * (D : ℝ))]`. Establish `hpow : ((4 : ℝ) * r) ^ D = Real.exp (D * Real.log (4 * r))`. Rewrite using `[Real.exp_nat_mul, Real.exp_log (by positivity)]`. Establish `hlog : Real.log (4 * r) = Real.log 4 + Real.log r` using `Real.log_mul (by norm_num) (by positivity)`. Establish `hP : 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3))`.

Rewrite using `[hpow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add, Real.exp_add]`. Use `_ ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Rewrite using `[hlog]`. Use polynomial arithmetic with `[mul_nonneg hD0 (mul_nonneg (sub_nonneg.2 hr1) hlogr), mul_nonneg hD0 (sub_nonneg.2 hlog4), mul_nonneg hD0 (sub_nonneg.2 hr1), mul_nonneg hr0.le hlogr]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem num_bound (r D : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3)))) :
    2 * D * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε ≤ 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have h2D : 2 * (D : ℝ) ≤ Real.exp (2 * D) := by linarith [Real.add_one_le_exp (2 * (D : ℝ))]
  have hpow : ((4 : ℝ) * r) ^ D = Real.exp (D * Real.log (4 * r)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hlog : Real.log (4 * r) = Real.log 4 + Real.log r :=
    Real.log_mul (by norm_num) (by positivity)
  have hP : 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) ≤
      Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
    rw [hpow]
    calc 2 * (D : ℝ) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D)
        ≤ Real.exp (2 * D) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D) := by
          gcongr
      _ = Real.exp (2 * D + D * Real.log (4 * r) + (r / 2 + 1) * D) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
          apply Real.exp_le_exp.2
          rw [hlog]
          nlinarith [mul_nonneg hD0 (mul_nonneg (sub_nonneg.2 hr1) hlogr),
            mul_nonneg hD0 (sub_nonneg.2 hlog4), mul_nonneg hD0 (sub_nonneg.2 hr1),
            mul_nonneg hr0.le hlogr]
  calc 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε
      ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) *
          Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3))) :=
        mul_le_mul hP hε hε0 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/- English proof (translation)
Establish `he1 : (2.7182818283 : ℝ) < Real.exp 1` using `Real.exp_one_gt_d9`. Establish `h7 : (7 : ℝ) ≤ Real.exp 3`. Establish `e : Real.exp 3 = Real.exp 1 ^ 3` using `by rw [← Real.exp_nat_mul]; norm_num`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h43 : (4.3 : ℝ) ≤ Real.exp 2`. Establish `e : Real.exp 2 = Real.exp 1 ^ 2` using `by rw [← Real.exp_nat_mul]; norm_num`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2g : (2 : ℝ) ^ g = Real.exp (g * Real.log 2)`.

Rewrite using `[Real.exp_nat_mul, Real.exp_log (by norm_num)]`. Establish `h43d : (4.3 : ℝ) ^ d ≤ Real.exp (d * 2)`. Rewrite using `[Real.exp_nat_mul]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2g]`. Use `gcongr`. Use `_ = Real.exp (3 + g * Real.log 2 + d * 2 + -t) := by simp only [Real.exp_add]`. Use `_ ≤ Real.exp (-K) := Real.exp_le_exp.2 (by linarith)`.
-/
theorem eps_bound (g d : ℕ) (t K : ℝ) (h : g * Real.log 2 + 2 * d + 3 + K ≤ t) :
    7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t) ≤ Real.exp (-K) := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h7 : (7 : ℝ) ≤ Real.exp 3 := by
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (7 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := by gcongr
  have h43 : (4.3 : ℝ) ≤ Real.exp 2 := by
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (4.3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := by gcongr
  have h2g : (2 : ℝ) ^ g = Real.exp (g * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h43d : (4.3 : ℝ) ^ d ≤ Real.exp (d * 2) := by
    rw [Real.exp_nat_mul]
    gcongr
  calc 7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t)
      ≤ Real.exp 3 * Real.exp (g * Real.log 2) * Real.exp (d * 2) * Real.exp (-t) := by
        rw [h2g]; gcongr
    _ = Real.exp (3 + g * Real.log 2 + d * 2 + -t) := by simp only [Real.exp_add]
    _ ≤ Real.exp (-K) := Real.exp_le_exp.2 (by linarith)

end ReciprocityTheory.ChartRestriction.G.I2
