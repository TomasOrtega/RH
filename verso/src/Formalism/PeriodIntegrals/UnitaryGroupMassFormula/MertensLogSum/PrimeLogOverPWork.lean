import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.LogFactorialEqSumLog

namespace PI.PrimeLogOverPWork

open Finset ArithmeticFunction Nat

def E : Finset ℕ := {4, 8, 16, 9, 27, 25}

/- English proof (translation)
Rewrite using `[show (4:ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0), vonMangoldt_apply_prime Nat.prime_two]`. Evaluate the numerical expressions.
-/
theorem vm4 : Λ 4 = Real.log 2 := by
  rw [show (4:ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_two]
  norm_num
/- English proof (translation)
Rewrite using `[show (8:ℕ) = 2 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num : (3:ℕ) ≠ 0), vonMangoldt_apply_prime Nat.prime_two]`. Evaluate the numerical expressions.
-/
theorem vm8 : Λ 8 = Real.log 2 := by
  rw [show (8:ℕ) = 2 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num : (3:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_two]
  norm_num
/- English proof (translation)
Rewrite using `[show (16:ℕ) = 2 ^ 4 by norm_num, vonMangoldt_apply_pow (by norm_num : (4:ℕ) ≠ 0), vonMangoldt_apply_prime Nat.prime_two]`. Evaluate the numerical expressions.
-/
theorem vm16 : Λ 16 = Real.log 2 := by
  rw [show (16:ℕ) = 2 ^ 4 by norm_num, vonMangoldt_apply_pow (by norm_num : (4:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_two]
  norm_num
/- English proof (translation)
Rewrite using `[show (9:ℕ) = 3 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0), vonMangoldt_apply_prime Nat.prime_three]`. Evaluate the numerical expressions.
-/
theorem vm9 : Λ 9 = Real.log 3 := by
  rw [show (9:ℕ) = 3 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_three]
  norm_num
/- English proof (translation)
Rewrite using `[show (27:ℕ) = 3 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num : (3:ℕ) ≠ 0), vonMangoldt_apply_prime Nat.prime_three]`. Evaluate the numerical expressions.
-/
theorem vm27 : Λ 27 = Real.log 3 := by
  rw [show (27:ℕ) = 3 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num : (3:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_three]
  norm_num
/- English proof (translation)
Rewrite using `[show (25:ℕ) = 5 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0), vonMangoldt_apply_prime Nat.prime_five]`. Evaluate the numerical expressions.
-/
theorem vm25 : Λ 25 = Real.log 5 := by
  rw [show (25:ℕ) = 5 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_five]
  norm_num

/- English proof (translation)
The claim follows from `mul_le_mul_of_nonneg_left (div_sub_one_le n d) vonMangoldt_nonneg`.
-/
theorem term_ge (n d : ℕ) : Λ d * ((n : ℝ) / d - 1) ≤ Λ d * ((n / d : ℕ) : ℝ) :=
  mul_le_mul_of_nonneg_left (div_sub_one_le n d) vonMangoldt_nonneg

/- English proof (translation)
Substitute `hc hx` using the available equality. Conclude with `term_ge n d`.
-/
private theorem vonMangoldt_mul_div_sub_one_le_floor_div (n d : ℕ) (c x : ℝ) (hc : Λ d = c) (hx : (d : ℝ) = x) :
    c * ((n : ℝ) / x - 1) ≤ c * ((n / d : ℕ) : ℝ) := by
  subst hc hx
  exact term_ge n d

/- English proof (translation)
Establish `hs : ∑ d ∈ E, Λ d * ((n / d : ℕ) : ℝ) = Λ 4 * ((n / 4 : ℕ) : ℝ) + (Λ 8 * ((n / 8 : ℕ) : ℝ) + (Λ 16 * ((n / 16 : ℕ) : ℝ) + (Λ 9 * ((n / 9 : ℕ) : ℝ) + (Λ 27 * ((n / 27 : ℕ) : ℝ) + Λ 25 * ((n / 25 : ℕ) : ℝ)))))`. Rewrite using `[E, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]`. Rewrite using `[hs, vm4, vm8, vm16, vm9, vm27, vm25]`. Establish `h4` using `vonMangoldt_mul_div_sub_one_le_floor_div n 4 (Real.log 2) 4 vm4 (by norm_num)`. Establish `h8` using `vonMangoldt_mul_div_sub_one_le_floor_div n 8 (Real.log 2) 8 vm8 (by norm_num)`.

Establish `h16` using `vonMangoldt_mul_div_sub_one_le_floor_div n 16 (Real.log 2) 16 vm16 (by norm_num)`. Establish `h9` using `vonMangoldt_mul_div_sub_one_le_floor_div n 9 (Real.log 3) 9 vm9 (by norm_num)`. Establish `h27` using `vonMangoldt_mul_div_sub_one_le_floor_div n 27 (Real.log 3) 27 vm27 (by norm_num)`. Establish `h25` using `vonMangoldt_mul_div_sub_one_le_floor_div n 25 (Real.log 5) 25 vm25 (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_E_ge (n : ℕ) :
    Real.log 2 * ((n : ℝ) * (7 / 16) - 3) + Real.log 3 * ((n : ℝ) * (4 / 27) - 2)
      + Real.log 5 * ((n : ℝ) / 25 - 1) ≤ ∑ d ∈ E, Λ d * ((n / d : ℕ) : ℝ) := by
  have hs : ∑ d ∈ E, Λ d * ((n / d : ℕ) : ℝ) =
      Λ 4 * ((n / 4 : ℕ) : ℝ) + (Λ 8 * ((n / 8 : ℕ) : ℝ) + (Λ 16 * ((n / 16 : ℕ) : ℝ) +
        (Λ 9 * ((n / 9 : ℕ) : ℝ) + (Λ 27 * ((n / 27 : ℕ) : ℝ) + Λ 25 * ((n / 25 : ℕ) : ℝ))))) := by
    rw [E, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton]
  rw [hs, vm4, vm8, vm16, vm9,
    vm27, vm25]
  have h4 := vonMangoldt_mul_div_sub_one_le_floor_div n 4 (Real.log 2) 4 vm4 (by norm_num)
  have h8 := vonMangoldt_mul_div_sub_one_le_floor_div n 8 (Real.log 2) 8 vm8 (by norm_num)
  have h16 := vonMangoldt_mul_div_sub_one_le_floor_div n 16 (Real.log 2) 16 vm16 (by norm_num)
  have h9 := vonMangoldt_mul_div_sub_one_le_floor_div n 9 (Real.log 3) 9 vm9 (by norm_num)
  have h27 := vonMangoldt_mul_div_sub_one_le_floor_div n 27 (Real.log 3) 27 vm27 (by norm_num)
  have h25 := vonMangoldt_mul_div_sub_one_le_floor_div n 25 (Real.log 5) 25 vm25 (by norm_num)
  linarith

/- English proof (translation)
Simplify using `[Chebyshev.theta]`.
-/
private theorem theta_eq_sum_log_primes (n : ℕ) :
    Chebyshev.theta n = ∑ p ∈ Ioc 0 n with p.Prime, Real.log p := by
  simp [Chebyshev.theta]

/- English proof (translation)
Rewrite using `[theta_eq_sum_log_primes, S, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Establish `hpp : p.Prime` using `(Finset.mem_filter.mp hp).2`. Establish `h` using `term_ge n p`.

Rewrite `h`, the goal using `[vonMangoldt_apply_prime hpp]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_primes_ge (n : ℕ) :
    (n : ℝ) * S n - Chebyshev.theta n
      ≤ ∑ d ∈ Ioc 0 n with d.Prime, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [theta_eq_sum_log_primes, S, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  have h := term_ge n p
  rw [vonMangoldt_apply_prime hpp] at h ⊢
  calc (n : ℝ) * (Real.log p / p) - Real.log p = Real.log p * ((n : ℝ) / p - 1) := by ring
    _ ≤ _ := h

/- English proof (translation)
Rewrite using `[log_factorial_eq]`. Establish `hdisj : Disjoint ({d ∈ Ioc 0 n | d.Prime} : Finset ℕ) E`. Rewrite using `[Finset.disjoint_right]`. Introduce `d hd`. Simplify using `only [E, Finset.mem_insert, Finset.mem_singleton] at hd`.

Simplify using `only [Finset.mem_filter, not_and]`. Introduce `_`. Apply the tactic sequence `rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num`. Establish `hsub : ({d ∈ Ioc 0 n | d.Prime} : Finset ℕ) ∪ E ⊆ Ioc 0 n`. Introduce `d hd`.

Break down `Finset.mem_union.mp hd with h | h` into its components or cases. Conclude with `(Finset.mem_filter.mp h).1`. Simplify using `only [E, Finset.mem_insert, Finset.mem_singleton] at h`. Rewrite using `[Finset.mem_Ioc]`. Apply the tactic sequence `rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> omega`.

Establish `hle` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun d => Λ d * ((n / d : ℕ) : ℝ)) (fun d _ _ => mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))`. Rewrite `hle` using `[Finset.sum_union hdisj]`. Establish `h1` using `sum_primes_ge n`. Establish `h2` using `sum_E_ge n`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_factorial_ge (n : ℕ) (hn : 27 ≤ n) :
    (n : ℝ) * S n - Chebyshev.theta n
      + (Real.log 2 * ((n : ℝ) * (7 / 16) - 3) + Real.log 3 * ((n : ℝ) * (4 / 27) - 2)
      + Real.log 5 * ((n : ℝ) / 25 - 1)) ≤ Real.log (n ! : ℝ) := by
  rw [log_factorial_eq]
  have hdisj : Disjoint ({d ∈ Ioc 0 n | d.Prime} : Finset ℕ) E := by
    rw [Finset.disjoint_right]
    intro d hd
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hd
    simp only [Finset.mem_filter, not_and]
    intro _
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hsub : ({d ∈ Ioc 0 n | d.Prime} : Finset ℕ) ∪ E ⊆ Ioc 0 n := by
    intro d hd
    rcases Finset.mem_union.mp hd with h | h
    · exact (Finset.mem_filter.mp h).1
    · simp only [E, Finset.mem_insert, Finset.mem_singleton] at h
      rw [Finset.mem_Ioc]
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun d => Λ d * ((n / d : ℕ) : ℝ))
    (fun d _ _ => mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
  rw [Finset.sum_union hdisj] at hle
  have h1 := sum_primes_ge n
  have h2 := sum_E_ge n
  linarith

/- English proof (translation)
Establish `hset : ({p ∈ Ioc 0 n | p.Prime} : Finset ℕ) = {p ∈ range (n + 1) | p.Prime}`. Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, h⟩, hp⟩`.

Conclude with `⟨by omega, hp⟩`. Introduce and unpack `⟨h, hp⟩`. Conclude with `⟨⟨hp.pos, by omega⟩, hp⟩`. Establish `hprod : ∑ p ∈ Ioc 0 n with p.Prime, Real.log p = Real.log (primorial n : ℝ)`. Rewrite using `[hset, primorial, Nat.cast_prod, Real.log_prod]`.

Introduce `p hp`. Conclude with `(Finset.mem_filter.mp hp).2.ne_zero` after adjusting the coercions. Rewrite using `[theta_eq_sum_log_primes, hprod]`. Establish `h4 : (primorial n : ℝ) ≤ (4 : ℝ) ^ n` using `by exact_mod_cast primorial_le_four_pow n`. Establish `hpos : (0 : ℝ) < primorial n` using `by exact_mod_cast primorial_pos n`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem theta_le_two_mul_log_two (n : ℕ) : Chebyshev.theta n ≤ 2 * n * Real.log 2 := by
  have hset : ({p ∈ Ioc 0 n | p.Prime} : Finset ℕ) = {p ∈ range (n + 1) | p.Prime} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, h⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨h, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
  have hprod : ∑ p ∈ Ioc 0 n with p.Prime, Real.log p = Real.log (primorial n : ℝ) := by
    rw [hset, primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  rw [theta_eq_sum_log_primes, hprod]
  have h4 : (primorial n : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast primorial_le_four_pow n
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  calc Real.log (primorial n : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := Real.log_le_log hpos h4
    _ = 2 * n * Real.log 2 := by
      rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring

/- English proof (translation)
Establish `hn' : (64 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hnpos : (0 : ℝ) < n` using `by linarith`. Establish `h1` using `log_factorial_ge n (by omega)`. Establish `h2` using `log_factorial_le n (by omega)`. Establish `hθ` using `theta_le_two_mul_log_two n`.

Establish `hL1 : Real.log 2 < 0.6931471808` using `Real.log_two_lt_d9`. Establish `hL0 : 0.6931471803 < Real.log 2` using `Real.log_two_gt_d9`. Establish `h3 : (19 : ℝ) / 12 * Real.log 2 ≤ Real.log 3`. Use `le_log_of_pow_le 3 19 12 (by norm_num) (by norm_num)` as an intermediate fact. Simplify using `using this`.

Establish `h5 : (51 : ℝ) / 22 * Real.log 2 ≤ Real.log 5`. Use `le_log_of_pow_le 5 51 22 (by norm_num) (by norm_num)` as an intermediate fact. Simplify using `using this`. Establish `h64 : Real.log 64 = 6 * Real.log 2`. Rewrite using `[show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]`.

Evaluate the numerical expressions. Establish `hlogn : Real.log n ≤ n / 64 - 1 + 6 * Real.log 2`. Establish `h` using `Real.log_le_sub_one_of_pos (div_pos hnpos (by norm_num : (0 : ℝ) < 64))`. Rewrite `h` using `[Real.log_div hnpos.ne' (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hnL : (n : ℝ) * Real.log 2 ≤ n * 0.6931471808` using `mul_le_mul_of_nonneg_left hL1.le hnpos.le`. Establish `h3' : (19 : ℝ) / 12 * Real.log 2 * ((n : ℝ) * (4 / 27) - 2) ≤ Real.log 3 * ((n : ℝ) * (4 / 27) - 2)` using `mul_le_mul_of_nonneg_right h3 (by linarith)`. Establish `h5' : (51 : ℝ) / 22 * Real.log 2 * ((n : ℝ) / 25 - 1) ≤ Real.log 5 * ((n : ℝ) / 25 - 1)` using `mul_le_mul_of_nonneg_right h5 (by linarith)`. Establish `key : (n : ℝ) * S n ≤ n * Real.log n` using `by linarith`. Conclude with `le_of_mul_le_mul_left key hnpos`.
-/
theorem S_le_large (n : ℕ) (hn : 64 ≤ n) : S n ≤ Real.log (n : ℝ) := by
  have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 := log_factorial_ge n (by omega)
  have h2 := log_factorial_le n (by omega)
  have hθ := theta_le_two_mul_log_two n
  have hL1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL0 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h3 : (19 : ℝ) / 12 * Real.log 2 ≤ Real.log 3 := by
    have := le_log_of_pow_le 3 19 12 (by norm_num) (by norm_num)
    simpa using this
  have h5 : (51 : ℝ) / 22 * Real.log 2 ≤ Real.log 5 := by
    have := le_log_of_pow_le 5 51 22 (by norm_num) (by norm_num)
    simpa using this
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlogn : Real.log n ≤ n / 64 - 1 + 6 * Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hnpos (by norm_num : (0 : ℝ) < 64))
    rw [Real.log_div hnpos.ne' (by norm_num)] at h
    linarith
  have hnL : (n : ℝ) * Real.log 2 ≤ n * 0.6931471808 := mul_le_mul_of_nonneg_left hL1.le hnpos.le
  have h3' : (19 : ℝ) / 12 * Real.log 2 * ((n : ℝ) * (4 / 27) - 2)
      ≤ Real.log 3 * ((n : ℝ) * (4 / 27) - 2) := mul_le_mul_of_nonneg_right h3 (by linarith)
  have h5' : (51 : ℝ) / 22 * Real.log 2 * ((n : ℝ) / 25 - 1)
      ≤ Real.log 5 * ((n : ℝ) / 25 - 1) := mul_le_mul_of_nonneg_right h5 (by linarith)
  have key : (n : ℝ) * S n ≤ n * Real.log n := by linarith
  exact le_of_mul_le_mul_left key hnpos

end PI.PrimeLogOverPWork
