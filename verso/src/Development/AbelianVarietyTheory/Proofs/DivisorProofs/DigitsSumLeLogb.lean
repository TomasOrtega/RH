import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hlogp : 0 < Real.log p` using `Real.log_pos hp1`. Establish `hpm : (0 : ℝ) < (p : ℝ) - 1` using `by linarith`. Establish `hdle : (d : ℝ) ≤ (p : ℝ) - 1`. Establish `h : ((d : ℝ) + 1) ≤ p` using `by exact_mod_cast hd`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set t : ℝ := (d : ℝ) / ((p : ℝ) - 1) with ht`. Establish `ht0 : 0 ≤ t` using `div_nonneg (by positivity) hpm.le`. Establish `ht1 : t ≤ 1` using `(div_le_one hpm).2 hdle`. Establish `hconc` using `(strictConcaveOn_log_Ioi.concaveOn).2 (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by simp only [Set.mem_Ioi]; linarith : (p : ℝ) ∈ Set.Ioi 0) (sub_nonneg.2 ht1) ht0 (by ring : (1 - t) + t = 1)`.

Simplify using `only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc`. Establish `heq : (1 - t) + t * p = (d : ℝ) + 1`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hconc` using `[heq]`. Establish `hmul : (d : ℝ) * Real.log p = ((p : ℝ) - 1) * (t * Real.log p)`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Real.logb, ← mul_div_assoc, le_div_iff₀ hlogp, hmul]`.

Conclude with `mul_le_mul_of_nonneg_left hconc hpm.le`.
-/
theorem digit_le_logb_succ (p d : ℕ) (hp : 1 < p) (hd : d < p) :
    (d : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((d : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdle : (d : ℝ) ≤ (p : ℝ) - 1 := by
    have h : ((d : ℝ) + 1) ≤ p := by exact_mod_cast hd
    linarith
  set t : ℝ := (d : ℝ) / ((p : ℝ) - 1) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) hpm.le
  have ht1 : t ≤ 1 := (div_le_one hpm).2 hdle
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2
    (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by simp only [Set.mem_Ioi]; linarith : (p : ℝ) ∈ Set.Ioi 0)
    (sub_nonneg.2 ht1) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc
  have heq : (1 - t) + t * p = (d : ℝ) + 1 := by
    rw [ht]; field_simp; ring
  rw [heq] at hconc
  have hmul : (d : ℝ) * Real.log p = ((p : ℝ) - 1) * (t * Real.log p) := by
    rw [ht]; field_simp
  rw [Real.logb, ← mul_div_assoc, le_div_iff₀ hlogp, hmul]
  exact mul_le_mul_of_nonneg_left hconc hpm.le

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hpm : (0 : ℝ) ≤ (p : ℝ) - 1` using `by linarith`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[Nat.digits_def' hp.one_lt hn, List.sum_cons, Nat.cast_add]`. Establish `hdiv` using `Nat.div_add_mod n p`. Establish `hdp : n % p < p` using `Nat.mod_lt n hp.pos`. Establish `ihq` using `ih (n / p) (Nat.div_lt_self hn hp.one_lt)`.

Establish `hd` using `digit_le_logb_succ p (n % p) hp.one_lt hdp`. Establish `hprod : (((n / p : ℕ) : ℝ) + 1) * (((n % p : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1`. Establish `h1 : (n / p + 1) * (n % p + 1) ≤ n + 1`. Establish `: (n / p) * (n % p + 1) ≤ (n / p) * p` using `Nat.mul_le_mul_left _ hdp`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `h1` after adjusting the coercions. Establish `hlog : Real.logb p (((n / p : ℕ) : ℝ) + 1) + Real.logb p (((n % p : ℕ) : ℝ) + 1) ≤ Real.logb p ((n : ℝ) + 1)`. Rewrite using `[← Real.logb_mul (by positivity) (by positivity)]`. Conclude with `Real.logb_le_logb_of_le hp1 (by positivity) hprod`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlog hpm]`.
-/
theorem digits_sum_le_logb (p n : ℕ) (hp : p.Prime) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' hp.one_lt hn, List.sum_cons, Nat.cast_add]
      have hdiv := Nat.div_add_mod n p
      have hdp : n % p < p := Nat.mod_lt n hp.pos
      have ihq := ih (n / p) (Nat.div_lt_self hn hp.one_lt)
      have hd := digit_le_logb_succ p (n % p) hp.one_lt hdp
      have hprod : (((n / p : ℕ) : ℝ) + 1) * (((n % p : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
        have h1 : (n / p + 1) * (n % p + 1) ≤ n + 1 := by
          have : (n / p) * (n % p + 1) ≤ (n / p) * p := Nat.mul_le_mul_left _ hdp
          nlinarith
        exact_mod_cast h1
      have hlog : Real.logb p (((n / p : ℕ) : ℝ) + 1) + Real.logb p (((n % p : ℕ) : ℝ) + 1)
          ≤ Real.logb p ((n : ℝ) + 1) := by
        rw [← Real.logb_mul (by positivity) (by positivity)]
        exact Real.logb_le_logb_of_le hp1 (by positivity) hprod
      nlinarith [mul_le_mul_of_nonneg_left hlog hpm]

end GlobalTheory
