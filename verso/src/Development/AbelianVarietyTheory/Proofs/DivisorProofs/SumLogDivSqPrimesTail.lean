import Mathlib

open Finset

namespace GlobalTheory

/- English proof (translation)
Establish `hB0 : 0 < B` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun p hp => ?_` and prove the remaining obligations. Take `⟨-, ⟨-, h2⟩, -⟩` from `Finset.mem_filter.1 hp`. Conclude with `div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) (pow_le_pow_left₀ hB0.le h2.le 2)`.

Use `_ = (∑ p ∈ (range (n + 1)).filter (fun p : ℕ => (p.Prime ∧ B < (p : ℝ)) ∧ (p : ℝ) ≤ 2 * B), Real.log p) / B ^ 2 := by`. Rewrite using `[Finset.sum_div]`. Use `_ ≤ Chebyshev.theta (2 * B) / B ^ 2 := by`. Use `div_le_div_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Unfold `Chebyshev.theta`.

Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p` and prove the remaining obligations. Introduce `p hp`. Take `⟨-, ⟨h1, -⟩, h3⟩` from `Finset.mem_filter.1 hp`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h1.pos, Nat.le_floor h3⟩, h1⟩`. Use `_ ≤ Real.log 4 * (2 * B) / B ^ 2 := div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) (by positivity)`.

Use `_ = 2 * Real.log 4 / B := by field_simp`.
-/
theorem sum_log_div_sq_primes_block (B : ℝ) (n : ℕ) (hB : 1 ≤ B) :
    ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => (p.Prime ∧ B < (p : ℝ)) ∧ (p : ℝ) ≤ 2 * B),
      Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
  have hB0 : 0 < B := by linarith
  calc ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => (p.Prime ∧ B < (p : ℝ)) ∧ (p : ℝ) ≤ 2 * B),
        Real.log p / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => (p.Prime ∧ B < (p : ℝ)) ∧ (p : ℝ) ≤ 2 * B),
        Real.log p / B ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨-, ⟨-, h2⟩, -⟩ := Finset.mem_filter.1 hp
        exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity)
          (pow_le_pow_left₀ hB0.le h2.le 2)
    _ = (∑ p ∈ (range (n + 1)).filter
          (fun p : ℕ => (p.Prime ∧ B < (p : ℝ)) ∧ (p : ℝ) ≤ 2 * B), Real.log p) / B ^ 2 := by
        rw [Finset.sum_div]
    _ ≤ Chebyshev.theta (2 * B) / B ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        unfold Chebyshev.theta
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
        intro p hp
        obtain ⟨-, ⟨h1, -⟩, h3⟩ := Finset.mem_filter.1 hp
        exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h1.pos, Nat.le_floor h3⟩, h1⟩
    _ ≤ Real.log 4 * (2 * B) / B ^ 2 :=
        div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) (by positivity)
    _ = 2 * Real.log 4 / B := by field_simp

/- English proof (translation)
Establish `h4 : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `B n hB hn`. Rewrite using `[Finset.filter_false_of_mem, Finset.sum_empty]`.

Check the signs of the components of the expression. Introduce `p hp h`. Establish `: (p : ℝ) ≤ n` using `by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)`. Simplify using `only [pow_zero, mul_one] at hn`. Combine the linear relations using `[h.2]`.

Consider the case `succ k ih`. Introduce `B n hB hn`. Establish `hB0 : 0 < B` using `by linarith`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ => (p : ℝ) ≤ 2 * B), Finset.filter_filter, Finset.filter_filter]`. Establish `h1` using `sum_log_div_sq_primes_block B n hB`.

Establish `h2` using `ih (2 * B) n (by linarith) (by rw [pow_succ] at hn; linarith)`. Establish `h3 : (range (n + 1)).filter (fun p : ℕ => (p.Prime ∧ B < (p : ℝ)) ∧ ¬ (p : ℝ) ≤ 2 * B) = (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ 2 * B < (p : ℝ))`. Use `Finset.filter_congr fun p _ => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, -⟩, c⟩`.

Conclude with `⟨a, not_le.1 c⟩`. Introduce and unpack `⟨a, c⟩`. Conclude with `⟨⟨a, by linarith⟩, not_le.2 c⟩`. Rewrite using `[h3]`. Establish `h5 : 4 * Real.log 4 / B = 2 * Real.log 4 / B + 4 * Real.log 4 / (2 * B)` using `by field_simp; ring`.

Rewrite using `[h5]`. Conclude with `add_le_add h1 h2`.
-/
theorem sum_log_div_sq_primes_gt_le_four_log_four_div (k : ℕ) : ∀ (B : ℝ) (n : ℕ), 1 ≤ B → (n : ℝ) ≤ B * 2 ^ k →
    ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ B < (p : ℝ)),
      Real.log p / (p : ℝ) ^ 2 ≤ 4 * Real.log 4 / B := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  induction k with
  | zero =>
    intro B n hB hn
    rw [Finset.filter_false_of_mem, Finset.sum_empty]
    · positivity
    · intro p hp h
      have : (p : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      simp only [pow_zero, mul_one] at hn
      linarith [h.2]
  | succ k ih =>
    intro B n hB hn
    have hB0 : 0 < B := by linarith
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ => (p : ℝ) ≤ 2 * B),
      Finset.filter_filter, Finset.filter_filter]
    have h1 := sum_log_div_sq_primes_block B n hB
    have h2 := ih (2 * B) n (by linarith) (by rw [pow_succ] at hn; linarith)
    have h3 : (range (n + 1)).filter
        (fun p : ℕ => (p.Prime ∧ B < (p : ℝ)) ∧ ¬ (p : ℝ) ≤ 2 * B) =
        (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ 2 * B < (p : ℝ)) := by
      refine Finset.filter_congr fun p _ => ?_
      constructor
      · rintro ⟨⟨a, -⟩, c⟩
        exact ⟨a, not_le.1 c⟩
      · rintro ⟨a, c⟩
        exact ⟨⟨a, by linarith⟩, not_le.2 c⟩
    rw [h3]
    have h5 : 4 * Real.log 4 / B = 2 * Real.log 4 / B + 4 * Real.log 4 / (2 * B) := by
      field_simp; ring
    rw [h5]
    exact add_le_add h1 h2

/- English proof (translation)
Introduce `B n hB`. Use `sum_log_div_sq_primes_gt_le_four_log_four_div n B n hB ?_` and prove the remaining obligations. Establish `h : (n : ℝ) ≤ 2 ^ n` using `by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le`. Establish `h2 : (0 : ℝ) < 2 ^ n` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_log_div_sq_primes_tail : ∀ (B : ℝ) (n : ℕ), 1 ≤ B →
    ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ B < (p : ℝ)),
      Real.log p / (p : ℝ) ^ 2 ≤ 4 * Real.log 4 / B := by
  intro B n hB
  refine sum_log_div_sq_primes_gt_le_four_log_four_div n B n hB ?_
  have h : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

end GlobalTheory
