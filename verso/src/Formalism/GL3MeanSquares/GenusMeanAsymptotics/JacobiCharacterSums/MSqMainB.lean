import Mathlib

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

/- English proof (translation)
Establish `hpt : ∀ n ∈ I, ∀ n' ∈ I, c n * c n' * A n n' ≤ ((if r n n' = 1 then c n * c n' else 0) + (if r n n' = nstar then c n * c n' else 0) + η * (c n * c n')) * P`. Introduce `n hn n' hn'`. Establish `hcc : 0 ≤ c n * c n'` using `mul_nonneg (hc n) (hc n')`. Establish `hAP` using `mul_le_mul_of_nonneg_left (hA n hn n' hn') hcc`. Establish `hηP : 0 ≤ η * (c n * c n') * P` using `mul_nonneg (mul_nonneg hη hcc) hP`.

Establish `hccP : 0 ≤ c n * c n' * P` using `mul_nonneg hcc hP`. Use `split_ifs with h1 h2 h2`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA2` using `mul_le_mul_of_nonneg_left (hA' n hn n' hn' h1 h2) hcc`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sq, Finset.sum_mul_sum]`. Simplify using `only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`.
-/
theorem meansq_split (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η) (nstar : ℕ)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
        (∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0) + η * (∑ n ∈ I, c n) ^ 2) * P := by
  have hpt : ∀ n ∈ I, ∀ n' ∈ I, c n * c n' * A n n' ≤
      ((if r n n' = 1 then c n * c n' else 0) + (if r n n' = nstar then c n * c n' else 0) +
        η * (c n * c n')) * P := by
    intro n hn n' hn'
    have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
    have hAP := mul_le_mul_of_nonneg_left (hA n hn n' hn') hcc
    have hηP : 0 ≤ η * (c n * c n') * P := mul_nonneg (mul_nonneg hη hcc) hP
    have hccP : 0 ≤ c n * c n' * P := mul_nonneg hcc hP
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · have hA2 := mul_le_mul_of_nonneg_left (hA' n hn n' hn' h1 h2) hcc
      linarith
  calc ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n'
      ≤ ∑ n ∈ I, ∑ n' ∈ I, ((if r n n' = 1 then c n * c n' else 0) +
          (if r n n' = nstar then c n * c n' else 0) + η * (c n * c n')) * P :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn'
    _ = _ := by
        rw [sq, Finset.sum_mul_sum]
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 < x` using `by linarith`. Establish `hε12 : 0 < ε / 12` using `by positivity`. Establish `hy1 : 1 < x ^ (ε / 12)` using `Real.one_lt_rpow hx1 hε12`. Establish `hy0 : 0 < x ^ (ε / 12)` using `by linarith`.

Establish `hK0 : 0 < 19200 / ε` using `by positivity`. Establish `hy : 19200 / ε ≤ x ^ (ε / 12)`. Establish `h` using `Real.rpow_le_rpow (Real.rpow_nonneg hK0.le (12 / ε)) hx hε12.le`. Rewrite `h` using `[← Real.rpow_mul hK0.le, show 12 / ε * (ε / 12) = 1 by field_simp, Real.rpow_one]`. Then use the resulting hypothesis. Establish `hlogx : Real.log x = 12 / ε * Real.log (x ^ (ε / 12))`.

Rewrite using `[Real.log_rpow hx0]`. Clear the denominators using the available nonvanishing facts. Establish `hy2 : x ^ (ε / 6) = (x ^ (ε / 12)) ^ 2`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlogy0 : 0 < Real.log (x ^ (ε / 12))` using `Real.log_pos hy1`. Establish `hlogy : Real.log (x ^ (ε / 12)) ≤ x ^ (ε / 12)` using `(Real.log_le_sub_one_of_pos hy0).trans (by linarith)`. Establish `key : 1600 * Real.log x ≤ Real.log X`.

Rewrite using `[hlogx]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hX _), Real.log_pow, Real.log_rpow hX]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pow_le_sqrt_of_rpow_le_log (ε : ℝ) (hε : 0 < ε) (x X : ℝ) (hx3 : 3 ≤ x) (hx : (19200 / ε) ^ (12 / ε) ≤ x)
    (hX : 0 < X) (hlog : x ^ (ε / 6) ≤ Real.log X) : x ^ 800 ≤ X ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hε12 : 0 < ε / 12 := by positivity
  have hy1 : 1 < x ^ (ε / 12) := Real.one_lt_rpow hx1 hε12
  have hy0 : 0 < x ^ (ε / 12) := by linarith
  have hK0 : 0 < 19200 / ε := by positivity
  have hy : 19200 / ε ≤ x ^ (ε / 12) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le (12 / ε)) hx hε12.le
    rwa [← Real.rpow_mul hK0.le, show 12 / ε * (ε / 12) = 1 by field_simp, Real.rpow_one] at h
  have hlogx : Real.log x = 12 / ε * Real.log (x ^ (ε / 12)) := by
    rw [Real.log_rpow hx0]
    field_simp
  have hy2 : x ^ (ε / 6) = (x ^ (ε / 12)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hlogy0 : 0 < Real.log (x ^ (ε / 12)) := Real.log_pos hy1
  have hlogy : Real.log (x ^ (ε / 12)) ≤ x ^ (ε / 12) :=
    (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  have key : 1600 * Real.log x ≤ Real.log X := by
    rw [hlogx]
    calc 1600 * (12 / ε * Real.log (x ^ (ε / 12))) = 19200 / ε * Real.log (x ^ (ε / 12)) := by ring
      _ ≤ x ^ (ε / 12) * Real.log (x ^ (ε / 12)) := mul_le_mul_of_nonneg_right hy hlogy0.le
      _ ≤ x ^ (ε / 12) * x ^ (ε / 12) := mul_le_mul_of_nonneg_left hlogy hy0.le
      _ = x ^ (ε / 6) := by rw [hy2]; ring
      _ ≤ Real.log X := hlog
  rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hX _), Real.log_pow,
    Real.log_rpow hX]
  push_cast
  linarith

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : (1 : ℝ) ≤ x` using `by linarith`. Establish `hL1 : 1 ≤ Real.log x`. Rewrite using `[Real.le_log_iff_exp_le hx0]`. Use `Real.exp_one_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL0 : 0 ≤ Real.log x` using `by linarith`. Establish `hLx : Real.log x ≤ x` using `(Real.log_le_sub_one_of_pos hx0).trans (by linarith)`. Establish `hsq : Real.sqrt x ≤ x`. Rewrite using `[Real.sqrt_le_iff]`.

Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[sq]`. Conclude with `le_mul_of_one_le_right hx0.le hx1`. Establish `hsq0 : 0 ≤ Real.sqrt x` using `Real.sqrt_nonneg x`.

Establish `hsx : Real.sqrt x ^ 2 = x` using `Real.sq_sqrt hx0.le`. Establish `ha0 : 0 ≤ x ^ (ε / 5)` using `Real.rpow_nonneg hx0.le _`. Establish `hab : x ^ (ε / 5) ≤ x ^ (1 / 5 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hL45 : Real.log x ≤ x ^ (4 / 5 : ℝ) / (4 / 5)` using `Real.log_le_rpow_div hx0.le (by norm_num)`. Establish `hL35 : Real.log x ≤ x ^ (3 / 5 : ℝ) / (3 / 5)` using `Real.log_le_rpow_div hx0.le (by norm_num)`.

Establish `hp45 : x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ) = x`. Rewrite using `[← Real.rpow_add hx0]`. Evaluate the numerical expressions. Establish `hp35 : (x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ) = x`. Rewrite using `[← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]`.

Evaluate the numerical expressions. Establish `hb0 : 0 ≤ x ^ (1 / 5 : ℝ)` using `Real.rpow_nonneg hx0.le _`. Establish `hc45 : 0 ≤ x ^ (4 / 5 : ℝ)` using `Real.rpow_nonneg hx0.le _`. Establish `hc35 : 0 ≤ x ^ (3 / 5 : ℝ)` using `Real.rpow_nonneg hx0.le _`. Establish `haL : x ^ (ε / 5) * Real.log x ≤ 5 / 4 * x`.

Combine the equalities or inequalities in the displayed calculation. Establish `haL2 : (x ^ (ε / 5) * Real.log x) ^ 2 ≤ 5 / 3 * x * Real.log x`. Establish `h1 : (x ^ (ε / 5)) ^ 2 ≤ (x ^ (1 / 5 : ℝ)) ^ 2` using `pow_le_pow_left₀ ha0 hab 2`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ hL0` to reduce the goal to its premises.

Conclude with `mul_le_mul h1 hL35 hL0 (sq_nonneg _)`. Use `_ = 5 / 3 * ((x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ)) * Real.log x := by ring`. Use `_ = 5 / 3 * x * Real.log x := by rw [hp35]`. Use `set T := Real.sqrt x + x ^ (ε / 5) * Real.log x with hTdef`. Establish `hT0 : 0 ≤ T` using `by positivity`.

Establish `hT : T ≤ 9 / 4 * x` using `by linarith`. Establish `hT2 : T ^ 2 ≤ 16 / 3 * x * Real.log x`. Establish `e : T ^ 2 = 2 * Real.sqrt x ^ 2 + 2 * (x ^ (ε / 5) * Real.log x) ^ 2 - (Real.sqrt x - x ^ (ε / 5) * Real.log x) ^ 2` using `by rw [hTdef]; ring`. Establish `hxL1 : x ≤ x * Real.log x` using `le_mul_of_one_le_right hx0.le hL1`. Establish `hs` using `sq_nonneg (Real.sqrt x - x ^ (ε / 5) * Real.log x)`.

Rewrite using `[e, hsx]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC3T : 0 ≤ C3 * T` using `hR0.trans hR`. Establish `hR2 : R ^ 2 ≤ C3 ^ 2 * (16 / 3 * x * Real.log x)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hRT : R ≤ |C3| * T` using `hR.trans (mul_le_mul_of_nonneg_right (le_abs_self C3) hT0)`. Establish `hxL : 0 ≤ x * Real.log x` using `mul_nonneg hx0.le hL0`. Establish `e1 : Sd ≤ |C4| * x * Real.log x`. Combine the equalities or inequalities in the displayed calculation. Establish `hC2 : 0 ≤ |C2|` using `abs_nonneg C2`.

Establish `hC3 : 0 ≤ |C3|` using `abs_nonneg C3`. Establish `e3 : 2 * (|C2| * Real.log x) * R ≤ 9 / 2 * (|C2| * |C3|) * (x * Real.log x)`. Establish `h1 : 0 ≤ 2 * (|C2| * Real.log x)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `e4 : 2 * (|C2| * Real.log x) ^ 2 ≤ 2 * C2 ^ 2 * (x * Real.log x)`.

Establish `: (|C2| * Real.log x) ^ 2 = C2 ^ 2 * (Real.log x * Real.log x)` using `by rw [mul_pow, sq_abs]; ring`. Rewrite using `[this]`. Establish `h2 : Real.log x * Real.log x ≤ x * Real.log x` using `mul_le_mul_of_nonneg_right hLx hL0`. Establish `h3` using `mul_le_mul_of_nonneg_left h2 (sq_nonneg C2)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e5 : x ^ (-3 : ℝ) * S1 ^ 2 ≤ C1 ^ 2 * (x * Real.log x)`. Establish `hS2 : S1 ^ 2 ≤ (C1 * x * Real.log x) ^ 2` using `pow_le_pow_left₀ hS0 hS1 2`. Establish `hx3 : x ^ (-3 : ℝ) = (x ^ 3)⁻¹`. Rewrite using `[Real.rpow_neg hx0.le]`. Use `norm_cast`.

Rewrite using `[hx3]`. Establish `hx30 : 0 < x ^ 3` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ hx0]`. Establish `h3 : Real.log x * Real.log x ≤ x * Real.log x * x` using `(mul_le_mul_of_nonneg_right hLx hL0).trans (le_mul_of_one_le_right hxL hx1)`.

Establish `h4` using `mul_le_mul_of_nonneg_left h3 (sq_nonneg C1)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos1 : 0 ≤ C3 ^ 2 * (x * Real.log x)` using `mul_nonneg (sq_nonneg _) hxL`. Establish `hpos2 : 0 ≤ |C2| * |C3| * (x * Real.log x)` using `mul_nonneg (mul_nonneg hC2 hC3) hxL`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem final_size (ε : ℝ) (hε1 : ε ≤ 1) (x : ℝ) (hx3 : 3 ≤ x) (C1 C2 C3 C4 S1 Sd R : ℝ)
    (hS0 : 0 ≤ S1) (hS1 : S1 ≤ C1 * x * Real.log x) (hSd : Sd ≤ C4 * x * Real.log x) (hR0 : 0 ≤ R)
    (hR : R ≤ C3 * (Real.sqrt x + x ^ (ε / 5) * Real.log x)) :
    Sd + R ^ 2 + (2 * (|C2| * Real.log x) ^ 2 + 2 * (|C2| * Real.log x) * R) + x ^ (-3 : ℝ) * S1 ^ 2 ≤
      (|C4| + 25 * C3 ^ 2 + 2 * C2 ^ 2 + 10 * |C2| * |C3| + C1 ^ 2) * x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ Real.log x := by linarith
  have hLx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hsq : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · rw [sq]
      exact le_mul_of_one_le_right hx0.le hx1
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have ha0 : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
  have hab : x ^ (ε / 5) ≤ x ^ (1 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hL45 : Real.log x ≤ x ^ (4 / 5 : ℝ) / (4 / 5) := Real.log_le_rpow_div hx0.le (by norm_num)
  have hL35 : Real.log x ≤ x ^ (3 / 5 : ℝ) / (3 / 5) := Real.log_le_rpow_div hx0.le (by norm_num)
  have hp45 : x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hp35 : (x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ) = x := by
    rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]; norm_num
  have hb0 : 0 ≤ x ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have hc45 : 0 ≤ x ^ (4 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have hc35 : 0 ≤ x ^ (3 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have haL : x ^ (ε / 5) * Real.log x ≤ 5 / 4 * x := by
    calc x ^ (ε / 5) * Real.log x ≤ x ^ (1 / 5 : ℝ) * (x ^ (4 / 5 : ℝ) / (4 / 5)) :=
          mul_le_mul hab hL45 hL0 hb0
      _ = 5 / 4 * (x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ)) := by ring
      _ = 5 / 4 * x := by rw [hp45]
  have haL2 : (x ^ (ε / 5) * Real.log x) ^ 2 ≤ 5 / 3 * x * Real.log x := by
    have h1 : (x ^ (ε / 5)) ^ 2 ≤ (x ^ (1 / 5 : ℝ)) ^ 2 := pow_le_pow_left₀ ha0 hab 2
    calc (x ^ (ε / 5) * Real.log x) ^ 2 = (x ^ (ε / 5)) ^ 2 * Real.log x * Real.log x := by ring
      _ ≤ (x ^ (1 / 5 : ℝ)) ^ 2 * (x ^ (3 / 5 : ℝ) / (3 / 5)) * Real.log x := by
          apply mul_le_mul_of_nonneg_right _ hL0
          exact mul_le_mul h1 hL35 hL0 (sq_nonneg _)
      _ = 5 / 3 * ((x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ)) * Real.log x := by ring
      _ = 5 / 3 * x * Real.log x := by rw [hp35]
  set T := Real.sqrt x + x ^ (ε / 5) * Real.log x with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hT : T ≤ 9 / 4 * x := by linarith
  have hT2 : T ^ 2 ≤ 16 / 3 * x * Real.log x := by
    have e : T ^ 2 = 2 * Real.sqrt x ^ 2 + 2 * (x ^ (ε / 5) * Real.log x) ^ 2 -
        (Real.sqrt x - x ^ (ε / 5) * Real.log x) ^ 2 := by rw [hTdef]; ring
    have hxL1 : x ≤ x * Real.log x := le_mul_of_one_le_right hx0.le hL1
    have hs := sq_nonneg (Real.sqrt x - x ^ (ε / 5) * Real.log x)
    rw [e, hsx]
    linarith
  have hC3T : 0 ≤ C3 * T := hR0.trans hR
  have hR2 : R ^ 2 ≤ C3 ^ 2 * (16 / 3 * x * Real.log x) := by
    calc R ^ 2 ≤ (C3 * T) ^ 2 := pow_le_pow_left₀ hR0 hR 2
      _ = C3 ^ 2 * T ^ 2 := by ring
      _ ≤ C3 ^ 2 * (16 / 3 * x * Real.log x) := mul_le_mul_of_nonneg_left hT2 (sq_nonneg _)
  have hRT : R ≤ |C3| * T := hR.trans (mul_le_mul_of_nonneg_right (le_abs_self C3) hT0)
  have hxL : 0 ≤ x * Real.log x := mul_nonneg hx0.le hL0
  have e1 : Sd ≤ |C4| * x * Real.log x := by
    calc Sd ≤ C4 * x * Real.log x := hSd
      _ = C4 * (x * Real.log x) := by ring
      _ ≤ |C4| * (x * Real.log x) := mul_le_mul_of_nonneg_right (le_abs_self C4) hxL
      _ = |C4| * x * Real.log x := by ring
  have hC2 : 0 ≤ |C2| := abs_nonneg C2
  have hC3 : 0 ≤ |C3| := abs_nonneg C3
  have e3 : 2 * (|C2| * Real.log x) * R ≤ 9 / 2 * (|C2| * |C3|) * (x * Real.log x) := by
    have h1 : 0 ≤ 2 * (|C2| * Real.log x) := by positivity
    calc 2 * (|C2| * Real.log x) * R ≤ 2 * (|C2| * Real.log x) * (|C3| * T) :=
          mul_le_mul_of_nonneg_left hRT h1
      _ ≤ 2 * (|C2| * Real.log x) * (|C3| * (9 / 4 * x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hC3) h1
      _ = 9 / 2 * (|C2| * |C3|) * (x * Real.log x) := by ring
  have e4 : 2 * (|C2| * Real.log x) ^ 2 ≤ 2 * C2 ^ 2 * (x * Real.log x) := by
    have : (|C2| * Real.log x) ^ 2 = C2 ^ 2 * (Real.log x * Real.log x) := by rw [mul_pow, sq_abs]; ring
    rw [this]
    have h2 : Real.log x * Real.log x ≤ x * Real.log x := mul_le_mul_of_nonneg_right hLx hL0
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg C2)
    linarith
  have e5 : x ^ (-3 : ℝ) * S1 ^ 2 ≤ C1 ^ 2 * (x * Real.log x) := by
    have hS2 : S1 ^ 2 ≤ (C1 * x * Real.log x) ^ 2 := pow_le_pow_left₀ hS0 hS1 2
    have hx3 : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
      rw [Real.rpow_neg hx0.le]; norm_cast
    rw [hx3]
    have hx30 : 0 < x ^ 3 := by positivity
    calc (x ^ 3)⁻¹ * S1 ^ 2 ≤ (x ^ 3)⁻¹ * (C1 * x * Real.log x) ^ 2 :=
          mul_le_mul_of_nonneg_left hS2 (inv_nonneg.mpr hx30.le)
      _ = C1 ^ 2 * (Real.log x * Real.log x) / x := by field_simp
      _ ≤ C1 ^ 2 * (x * Real.log x) := by
          rw [div_le_iff₀ hx0]
          have h3 : Real.log x * Real.log x ≤ x * Real.log x * x :=
            (mul_le_mul_of_nonneg_right hLx hL0).trans (le_mul_of_one_le_right hxL hx1)
          have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg C1)
          linarith
  have hpos1 : 0 ≤ C3 ^ 2 * (x * Real.log x) := mul_nonneg (sq_nonneg _) hxL
  have hpos2 : 0 ≤ |C2| * |C3| * (x * Real.log x) := mul_nonneg (mul_nonneg hC2 hC3) hxL
  linarith

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
