import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

open Polynomial in

/- English proof (translation)
Introduce `N x a δ hδ`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Conclude with `⟨a, le_rfl, by linarith, by simp⟩`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `he : (2 : ℝ) < Real.exp 1` using `lt_trans (by norm_num) Real.exp_one_gt_d9`. Establish `he0 : (0 : ℝ) < Real.exp 1` using `by linarith`. Use `set m : ℝ := δ / (2 * Real.exp 1) with hm`. Establish `hm0 : 0 < m` using `by positivity`. Set `P : ℝ[X]` to `∏ i : Fin N, (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))`.

Establish `hlc : P.leadingCoeff = Real.exp 1 ^ N`. Simplify using `only [P, leadingCoeff_prod, leadingCoeff_linear he0.ne']`. Simplify using the standard rewrite rules. Establish `hdeg : P.degree ≤ N`. Establish `: P.degree = ∑ _i : Fin N, (1 : WithBot ℕ)`.

Simplify using `only [P, degree_prod, degree_linear he0.ne']`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1`. Introduce `t ht`.

Establish `h1` using `hcon (a + δ / 2 + δ / 2 * t) (by nlinarith [ht.1]) (by nlinarith [ht.2])`. Establish `h2 : |P.eval t| = (∏ i, |a + δ / 2 + δ / 2 * t - x i|) / m ^ N`. Simplify using `only [P, eval_prod, Finset.abs_prod]`. Establish `: ∀ i : Fin N, |eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))| = |a + δ / 2 + δ / 2 * t - x i| / m`. Introduce `i`.

Establish `: eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m)) = (a + δ / 2 + δ / 2 * t - x i) / m`. Simplify using `only [eval_add, eval_mul, eval_C, eval_X, hm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, abs_div, abs_of_pos hm0]`.

Simplify using `only [this, Finset.prod_div_distrib]`. Simplify using the standard rewrite rules. Rewrite using `[h2, div_le_one (by positivity)]`. Conclude with `h1.le`. Establish `h3` using `Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdeg hb`.

Rewrite `h3` using `[hlc]`. Establish `h4 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N` using `pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)`. Establish `h5 : (2 : ℝ) ^ N < Real.exp 1 ^ N` using `pow_lt_pow_left₀ he (by norm_num) hN.ne'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_prod_abs_sub_ge_on_segment : ∀ (N : ℕ) (x : Fin N → ℝ) (a δ : ℝ), 0 < δ →
    ∃ r : ℝ, a ≤ r ∧ r ≤ a + δ ∧ (δ / (2 * Real.exp 1)) ^ N ≤ ∏ i, |r - x i| := by
  intro N x a δ hδ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨a, le_rfl, by linarith, by simp⟩
  by_contra hcon
  push Not at hcon
  have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  set m : ℝ := δ / (2 * Real.exp 1) with hm
  have hm0 : 0 < m := by positivity
  let P : ℝ[X] := ∏ i : Fin N, (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
  have hlc : P.leadingCoeff = Real.exp 1 ^ N := by
    simp only [P, leadingCoeff_prod, leadingCoeff_linear he0.ne']
    simp
  have hdeg : P.degree ≤ N := by
    have : P.degree = ∑ _i : Fin N, (1 : WithBot ℕ) := by
      simp only [P, degree_prod, degree_linear he0.ne']
    rw [this]; simp
  have hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1 := by
    intro t ht
    have h1 := hcon (a + δ / 2 + δ / 2 * t) (by nlinarith [ht.1]) (by nlinarith [ht.2])
    have h2 : |P.eval t| = (∏ i, |a + δ / 2 + δ / 2 * t - x i|) / m ^ N := by
      simp only [P, eval_prod, Finset.abs_prod]
      have : ∀ i : Fin N, |eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))|
          = |a + δ / 2 + δ / 2 * t - x i| / m := by
        intro i
        have : eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
            = (a + δ / 2 + δ / 2 * t - x i) / m := by
          simp only [eval_add, eval_mul, eval_C, eval_X, hm]
          field_simp
          ring
        rw [this, abs_div, abs_of_pos hm0]
      simp only [this, Finset.prod_div_distrib]
      simp
    rw [h2, div_le_one (by positivity)]
    exact h1.le
  have h3 := Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdeg hb
  rw [hlc] at h3
  have h4 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h5 : (2 : ℝ) ^ N < Real.exp 1 ^ N := pow_lt_pow_left₀ he (by norm_num) hN.ne'
  linarith

end GlobalTheory
