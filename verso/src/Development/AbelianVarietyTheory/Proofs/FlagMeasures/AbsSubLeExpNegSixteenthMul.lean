import Mathlib

open Matrix Finset Real

namespace GlobalTheory

/- English proof (translation)
Introduce `D Ds n f hD hDs hn hf h`. Establish `hn16 : (16:ℝ) ≤ n`. Use `Real.add_one_le_exp (15:ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : 0 < n` using `by linarith`.

Establish `hL : 15 ≤ Real.log n`. Use `Real.log_le_log (Real.exp_pos 15) hn` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `hLn : Real.log n ≤ n`. Use `Real.log_le_sub_one_of_pos hn0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnf : 16 ≤ n * f` using `by nlinarith`. Establish `ha : 240 ≤ n * f * Real.log n` using `by nlinarith`. Establish `hnn : n * f * Real.log n ≤ n ^ 2 * f`. Use `mul_le_mul_of_nonneg_left hLn (by linarith : (0:ℝ) ≤ n * f)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hlog8 : Real.log 8 ≤ 7`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8); linarith` as an intermediate fact. Establish `hT8 : Real.exp (-(1 / 16) * n * f * Real.log n - Real.log 8) = Real.exp (-(1 / 16) * n * f * Real.log n) / 8`. Rewrite using `[Real.exp_sub, Real.exp_log (by norm_num)]`.

Establish `e1 : Real.exp (-(1 / 4) * n * f * Real.log n) ≤ Real.exp (-(1 / 16) * n * f * Real.log n) / 8`. Rewrite using `[← hT8]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : Real.exp (-n ^ 2 * f) ≤ Real.exp (-(1 / 16) * n * f * Real.log n) / 8`.

Rewrite using `[← hT8]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hT1 : Real.exp (-(1 / 16) * n * f * Real.log n) ≤ 1`. Apply `Real.exp_le_one_iff.mpr` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `hδ0 : 0 ≤ Real.exp (-n ^ 2 * f)` using `(Real.exp_pos _).le`. Establish `hδ : Real.exp (-n ^ 2 * f) ≤ 1 / 2` using `by linarith`. Establish `hX : 0 ≤ |D - Ds|` using `abs_nonneg _`. Establish `hD' : D ≤ Ds + |D - Ds|` using `by have := le_abs_self (D - Ds); linarith`.

Establish `p1` using `mul_le_mul_of_nonneg_left hD' hδ0`. Establish `p2` using `mul_le_mul_of_nonneg_right hδ hX`. Establish `p3` using `mul_le_mul_of_nonneg_right e1 hDs`. Establish `p4` using `mul_le_mul_of_nonneg_right e2 hDs`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem abs_sub_le_exp_neg_sixteenth_mul :
    ∀ (D Ds n f : ℝ), 0 ≤ D → 0 ≤ Ds → Real.exp 15 ≤ n → 1 ≤ f → |D - Ds| ≤ (2 * Real.exp (-(1 / 4) * n * f * Real.log n) + Real.exp (-n ^ 2 * f)) * Ds + Real.exp (-n ^ 2 * f) * D → |D - Ds| ≤ Real.exp (-(1 / 16) * n * f * Real.log n) * Ds := by
  intro D Ds n f hD hDs hn hf h
  have hn16 : (16:ℝ) ≤ n := by
    have := Real.add_one_le_exp (15:ℝ); linarith
  have hn0 : 0 < n := by linarith
  have hL : 15 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 15) hn
    rwa [Real.log_exp] at this
  have hLn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hnf : 16 ≤ n * f := by nlinarith
  have ha : 240 ≤ n * f * Real.log n := by nlinarith
  have hnn : n * f * Real.log n ≤ n ^ 2 * f := by
    have := mul_le_mul_of_nonneg_left hLn (by linarith : (0:ℝ) ≤ n * f)
    nlinarith
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8); linarith
  have hT8 : Real.exp (-(1 / 16) * n * f * Real.log n - Real.log 8) =
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have e1 : Real.exp (-(1 / 4) * n * f * Real.log n) ≤
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have e2 : Real.exp (-n ^ 2 * f) ≤ Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have hT1 : Real.exp (-(1 / 16) * n * f * Real.log n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; nlinarith
  have hδ0 : 0 ≤ Real.exp (-n ^ 2 * f) := (Real.exp_pos _).le
  have hδ : Real.exp (-n ^ 2 * f) ≤ 1 / 2 := by linarith
  have hX : 0 ≤ |D - Ds| := abs_nonneg _
  have hD' : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have p1 := mul_le_mul_of_nonneg_left hD' hδ0
  have p2 := mul_le_mul_of_nonneg_right hδ hX
  have p3 := mul_le_mul_of_nonneg_right e1 hDs
  have p4 := mul_le_mul_of_nonneg_right e2 hDs
  nlinarith

end GlobalTheory
