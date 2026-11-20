import Mathlib
open Complex Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `e θ g s he hs hθ hg`. Establish `h1` using `hg s hs`. Establish `he' : (1 : ℝ) ≤ e` using `by exact_mod_cast he`. Establish `h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ ((2 * (e : ℝ) + s) - 1)` using `Real.summable_one_div_nat_rpow.mpr (by linarith)`. Use `Summable.of_norm_bounded ((h1.add h2).div_const 2) ?_` and prove the remaining obligations.

Introduce `n`. Rewrite using `[LSeries.norm_term_eq]`. Use `split_ifs with hn`. Check the signs of the components of the expression. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`.

Establish `e1 : (((2 * e + 1 : ℕ) : ℝ) + s) = (2 * (e : ℝ) + s) + 1` using `by push_cast; ring`. Rewrite using `[Complex.ofReal_re, e1, Real.rpow_add_one hn'.ne', Real.rpow_sub_one hn'.ne']`. Establish `hN : (0 : ℝ) < (n : ℝ) ^ (2 * (e : ℝ) + s)` using `Real.rpow_pos_of_pos hn' _`. Generalize the expression as in `(n : ℝ) ^ (2 * (e : ℝ) + s) = N at hN ⊢`. Establish `hb : ‖θ n * g n‖ ≤ ‖g n‖`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hθ n)`. Combine the equalities or inequalities in the displayed calculation. Establish `: (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 - ‖g n‖ / N = (‖g n‖ - n) ^ 2 / (2 * N * n)` using `by field_simp; ring`. Establish `h3 : 0 ≤ (‖g n‖ - n) ^ 2 / (2 * N * n)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lSeriesSummable_bounded_mul_of_summable_normSq :
    ∀ (e : ℕ) (θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => θ n * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e θ g s he hs hθ hg
  have h1 := hg s hs
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ ((2 * (e : ℝ) + s) - 1) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) ?_
  intro n
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have e1 : (((2 * e + 1 : ℕ) : ℝ) + s) = (2 * (e : ℝ) + s) + 1 := by push_cast; ring
    rw [Complex.ofReal_re, e1, Real.rpow_add_one hn'.ne', Real.rpow_sub_one hn'.ne']
    have hN : (0 : ℝ) < (n : ℝ) ^ (2 * (e : ℝ) + s) := Real.rpow_pos_of_pos hn' _
    generalize (n : ℝ) ^ (2 * (e : ℝ) + s) = N at hN ⊢
    have hb : ‖θ n * g n‖ ≤ ‖g n‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hθ n)
    calc ‖θ n * g n‖ / N ≤ ‖g n‖ / N := by gcongr
      _ ≤ (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 := by
        have : (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 - ‖g n‖ / N
            = (‖g n‖ - n) ^ 2 / (2 * N * n) := by field_simp; ring
        have h3 : 0 ≤ (‖g n‖ - n) ^ 2 / (2 * N * n) := by positivity
        linarith

end GlobalTheory
